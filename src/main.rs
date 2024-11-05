use std::io::Write;

use pl4::{backend::{compiling::compiler::Compiler, instructions::Chunk, vm::VM}, frontend::{parsing::parser::Parser, tokenizing::scanner::Scanner, typechecking::typechecker::TypeChecker}};

fn compile(source:&str)->Option<Chunk>{
    let Ok(tokens) = Scanner::new(source).scan() else {
        return None;
    };
    let parser = Parser::new(tokens);
    let Ok(stmts) = parser.parse() else{
        return None;
    };
    let typechecker = TypeChecker::default();
    let Ok(stmts) = typechecker.check(stmts) else {
        return None;
    };
    let Ok(code) = Compiler::default().compile(stmts) else {
        return None;
    };
    Some(code)
}
fn repl(){
    let mut vm = VM::new(Chunk::default());
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
