use std::io::Write;

use pl4::{
    backend::{compiling::compiler::Compiler, instructions::Program, vm::VM}, frontend::{ast_lowering::{ast_lower::AstLowerer, hir::DefIdProvider, name_finding::NameFinder}, 
    parsing::parser::Parser, tokenizing::scanner::Scanner, typechecking::{checking::check::TypeChecker, types::collect::ItemCollector}}, GlobalSymbols, SymbolInterner
};

fn compile(source:&str)->Option<Program>{
    let Ok(tokens) = Scanner::new(source).scan() else {
        return None;
    };
    let mut interner = SymbolInterner::new();
    let parser = Parser::new(tokens,&mut interner);
    let Ok(stmts) = parser.parse() else{
        return None;
    };
    let mut def_id_provider = DefIdProvider::new();
    let Ok((names_found,name_scopes)) = NameFinder::new(&mut interner,&mut def_id_provider).find_names(&stmts) else {
        return None;
    };
    let ast_lower = AstLowerer::new(&mut interner,names_found,name_scopes);
    let Ok(hir) = ast_lower.lower(stmts) else {
        return None;
    };

    let item_collector = ItemCollector::new(&interner);
    let context = item_collector.collect(&hir.items);
    let symbols = GlobalSymbols::new(&mut interner);
    let type_checker = TypeChecker::new(&context,&hir.items,&symbols,&hir.defs_to_items,&interner);
    let Ok(()) = type_checker.check(&hir.stmts) else {
        return None;
    };
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
