use std::io::Write;

use pl4::{
    backend::{compiling::compiler::Compiler, instructions::Program, vm::VM}, frontend::{ast_lowering::{ast_lower::AstLowerer, hir::DefIdProvider,name_finding::NameFinder}, hir_lowering::ThirLower, parsing::parser::Parser, tokenizing::scanner::Scanner, typechecking::{checking::check::TypeChecker, items::item_check::ItemCheck, types::collect::ItemCollector}}, GlobalSymbols, SymbolInterner
};

fn compile(source:&str)->Option<Program>{
    let Ok(tokens) = Scanner::new(source).scan() else {
        return None;
    };
    let mut interner = SymbolInterner::new();
    let symbols = GlobalSymbols::new(&mut interner);
    let parser = Parser::new(tokens,&mut interner);
    let Ok(stmts) = parser.parse() else{
        return None;
    };
    let mut def_id_provider = DefIdProvider::new();
    let (names_found,name_scopes) = NameFinder::new(&mut interner,&mut def_id_provider,&symbols).find_names(&stmts).ok()?;

    let ast_lower = AstLowerer::new(&mut interner,names_found,name_scopes);
    let hir = ast_lower.lower(stmts).ok()?;
    let item_collector = ItemCollector::new(&interner,&symbols,&hir.items,&hir);
    let (context,error_reporter) = item_collector.collect();
    ItemCheck::new(&context,&interner,&error_reporter).check_items(hir.items.iter()).ok()?;
    let type_checker = TypeChecker::new(&context,&symbols,&hir.bodies,&interner);
    let type_check_results = type_checker.check(hir.items.iter()).ok()?;
    let _thir = ThirLower::new(type_check_results,&context,&interner).lower_bodies(hir.bodies,hir.body_owners).ok()?;
    let Ok(code) = Compiler::new().compile() else {
        return None;
    };
    Some(code)
}
fn repl(){
    let mut vm = VM::new(Program::default());
    loop{
        let mut source = String::new();
        print!(">>>");
        if let Err(err) = std::io::stdout().flush().map(|_| std::io::stdin().read_line(&mut source)){
            eprintln!("{}",err);
            continue;
        };
        if let Some(code) = compile(&source) {
            vm.reset(code);
            let _ = vm.run();   
        }
    }
}
fn run_file(filepath:&str){
    let source = match std::fs::read_to_string(filepath){
        Ok(source) => source,
        Err(error) => {
            eprintln!("{}",error);
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
    }
    else{
        run_file(&args[0]);
    }
}
