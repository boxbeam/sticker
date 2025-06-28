use std::fs;

use untwine::{parser::parser, pretty::PrettyOptions};

mod parser;
mod runtime;

fn main() {
    let filename = std::env::args().nth(1).unwrap();
    let content = fs::read_to_string(filename).unwrap();
    let ast = match untwine::parse_pretty(parser::program, &content, PrettyOptions::default()) {
        Ok(ast) => ast,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    };
    let mut runtime_builder = runtime::RuntimeBuilder::default();
    runtime_builder.register_default_builtins();
    runtime_builder.populate_from_ast(ast).unwrap();
    let mut runtime = runtime_builder.build().unwrap();
    runtime.call_by_name("main").unwrap();
}
