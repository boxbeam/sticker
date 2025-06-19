use std::{num::ParseIntError, ops::Deref};
use thiserror::Error;
use untwine::prelude::*;

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
}

#[derive(Debug, Clone)]
pub struct Function(String);

impl Deref for Function {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    Literal(Literal),
    Function(Function),
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub body: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<FunctionDef>,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Parser(#[from] ParserError),

    #[error(transparent)]
    ParseInt(#[from] ParseIntError),
}

parser! {
    [error = Error]

    sep = #{|c| c.is_whitespace()}+;

    lit = match {
        num = <"-"? '0'-'9'+> => Literal::Int(num.parse()?)
    } -> Literal;

    ident: ident=<{|c| c.is_ascii_alphabetic() || "+-*/$_=".contains(*c)}+> -> String { ident.into() }

    function_body = "{" sep? item$sep* sep? "}" -> Vec<Item>;

    item = (#[convert(Item::Literal)] lit | #[convert(Item::Function)] function_call) -> Item;

    function_call: name=ident -> Function { Function(name) }

    function_def: "fn" sep name=ident sep? body=function_body -> FunctionDef {
        FunctionDef { name, body }
    }

    pub program: functions=function_def$(sep?)* sep? -> Program { Program { functions } }
}
