use std::io::Write;

use pl4::{
    ErrorReporter, GlobalSymbols, SymbolInterner,
    backend::{codegen::Codegen, compiling::compiler::Compiler, instructions::Program, vm::VM},
    frontend::{
        ast_lowering::{ast_lower::AstLowerer, hir::DefIdProvider, name_finding::NameFinder},
        hir_lowering::ThirLower,
        parsing::parser::Parser,
        tokenizing::scanner::Scanner,
        typechecking::{
            checking::check::TypeChecker, items::item_check::ItemCheck,
            types::collect::ItemCollector,
        },
    },
    middle::mir::{
        debug::DebugMir,
        passes::{
            MirPass, const_branch::ConstBranch, const_prop::ConstProp, pass_manager::PassManager,
            remove_unreachable_branches::RemoveUnreachableBranches, simplify_cfg::SimplifyCfg,
        },
    },
    thir_lowering::MirBuild,
};

fn compile(source: &str) -> Option<Program> {
    let Ok(tokens) = Scanner::new(source).scan() else {
        return None;
    };
    let mut interner = SymbolInterner::new();
    let symbols = GlobalSymbols::new(&mut interner);
    let parser = Parser::new(tokens, &mut interner);
    let Ok(stmts) = parser.parse() else {
        return None;
    };
    let mut def_id_provider = DefIdProvider::new();
    let (names_found, name_scopes) = NameFinder::new(&mut interner, &mut def_id_provider, &symbols)
        .find_names(&stmts)
        .ok()?;

    let ast_lower = AstLowerer::new(&mut interner, names_found, name_scopes);
    let hir = ast_lower.lower(stmts).ok()?;
    let error_reporter = ErrorReporter::new(true);
    let item_collector = ItemCollector::new(&interner, &symbols, &hir.items, &hir, &error_reporter);
    let context = item_collector.collect();
    ItemCheck::new(&context, &interner, &error_reporter)
        .check_items(hir.items.iter())
        .ok()?;
    let type_checker = TypeChecker::new(&context, &symbols, &hir.bodies, &interner);
    let type_check_results = type_checker.check(hir.items.iter()).ok()?;
    let thir = ThirLower::new(type_check_results, &context, &interner)
        .lower_bodies(&hir.bodies, hir.owner_to_bodies.clone())
        .ok()?;
    let mut mir = MirBuild::new(thir, &context).lower(hir.body_owners.clone());

    let passes: &[&dyn MirPass] = &[
        &SimplifyCfg as &dyn MirPass,
        &RemoveUnreachableBranches,
        &ConstProp,
        &ConstBranch,
        &SimplifyCfg,
    ];

    let pass_manager = PassManager::new_debug(&interner);
    for (_, body) in mir.bodies.index_value_iter_mut() {
        //pass_manager.run_single_pass(&ConstProp, &context, body);
        pass_manager.run_passes(passes, &context, body);
    }
    println!(
        "Final mir\n{}",
        DebugMir::new(&context, &interner).debug(mir.bodies.iter())
    );
    Codegen::new(mir).generate();
    let Ok(code) = Compiler::new().compile() else {
        return None;
    };
    Some(code)
}
fn repl() {
    let mut vm = VM::new(Program::default());
    loop {
        let mut source = String::new();
        print!(">>>");
        if let Err(err) = std::io::stdout()
            .flush()
            .map(|_| std::io::stdin().read_line(&mut source))
        {
            eprintln!("{err}");
            continue;
        };
        if let Some(code) = compile(&source) {
            vm.reset(code);
            let _ = vm.run();
        }
    }
}
fn run_file(filepath: &str) {
    let source = match std::fs::read_to_string(filepath) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("{error}");
            return;
        }
    };
    let Some(code) = compile(&source) else {
        return;
    };
    let mut vm = VM::new(code);
    let _ = vm.run();
}
fn main() {
    let mut args = std::env::args().collect::<Vec<String>>();
    args.remove(0);
    if args.is_empty() {
        repl();
    } else {
        run_file(&args[0]);
    }
}
