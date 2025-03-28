use std::io::Write;

use pl4::{backend::{compiling::compiler::Compiler, instructions::Program, vm::VM}, frontend::{ast_lowering::{ast_lower::AstLowerer, name_finding::NameFinder, SymbolInterner}, parsing::parser::Parser, tokenizing::scanner::Scanner, typechecking::typechecker::TypeChecker}};

fn compile(source:&str)->Option<Program>{
    let Ok(tokens) = Scanner::new(source).scan() else {
        return None;
    };
    let parser = Parser::new(tokens);
    let Ok(stmts) = parser.parse() else{
        return None;
    };
    let mut interner = SymbolInterner::new();
    let Ok((names_found,items_to_lower)) = NameFinder::new(&mut interner).find_names(&stmts) else {
        return None;
    };
    let ast_lower = AstLowerer::new(&mut interner,names_found);

    let Ok((items,stmts)) = ast_lower.lower(stmts) else {
        return None;
    };
    let typechecker = TypeChecker::new(&interner);
    let Ok((context,stmts)) = typechecker.check(items,stmts) else {
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
