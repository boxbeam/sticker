use std::{num::ParseIntError, ops::Deref};
use thiserror::Error;
use untwine::prelude::*;

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    String(String),
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
    Block(Block),
}

#[derive(Debug, Clone)]
pub struct Block(pub Vec<Item>);

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<FunctionDef>,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Unknown escape sequence: \"{0}\"")]
    UnknownEscapeSequence(String),

    #[error(transparent)]
    Parser(#[from] ParserError),

    #[error(transparent)]
    ParseInt(#[from] ParseIntError),
}

parser! {
    [error = Error]

    sep = #{|c| c.is_whitespace()}+;

    char: seq=<"\\" . | [^ "\""]> -> char {
        match seq {
            "\\\\" => '\\',
            "\\n" => '\n',
            "\\r" => '\r',
            "\\t" => '\t',
            _ if seq.len() == 1 => seq.chars().next().unwrap(),
            _ => return Err(Error::UnknownEscapeSequence(seq.into()))
        }
    }

    lit = match {
        num = <"-"? '0'-'9'+> => Literal::Int(num.parse()?),
        '"' chars=(char*) '"' => Literal::String(chars.into_iter().collect())
    } -> Literal;

    ident: ident=<{|c| c.is_ascii_alphabetic() || "+-*/$_=".contains(*c)}+> -> String { ident.into() }

    block = "{" sep? #[convert(Block)] item$sep* sep? "}" -> Block;

    item = (#[convert(Item::Literal)] lit | #[convert(Item::Function)] function_call | #[convert(Item::Block)] block) -> Item;

    function_call: name=ident -> Function { Function(name) }

    function_def: "fn" sep name=ident sep? body=block -> FunctionDef {
        FunctionDef { name, body }
    }

    pub program: functions=function_def$(sep?)* sep? -> Program { Program { functions } }
}
