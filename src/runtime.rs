use std::{
    collections::HashMap,
    fmt::{Display, write},
    io::BufRead,
    ops::Deref,
    rc::Rc,
};

use thiserror::Error;

use crate::parser;

#[derive(Debug, Error)]
pub enum CompilationError {
    #[error("Unknown function name \"{0}\"")]
    UnknownFunction(String),
}

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("Type mismatch: expected {expected} but got {found}")]
    TypeMismatch { expected: Type, found: Type },

    #[error(transparent)]
    Io(#[from] std::io::Error),
}

#[derive(Clone, Debug)]
enum Value {
    Int(i64),
    Bool(bool),
    String(String),
}

impl Value {
    fn get_type(&self) -> Type {
        match self {
            Value::Int(_) => Type::Int,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum BasicType {
    Int,
    Bool,
    String,
}

impl Display for BasicType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BasicType::Int => write!(f, "int"),
            BasicType::Bool => write!(f, "bool"),
            BasicType::String => write!(f, "string"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum Type {
    Basic(BasicType),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(val) => write!(f, "{val}"),
            Value::Bool(val) => write!(f, "{val}"),
            Value::String(val) => write!(f, "{val}"),
        }
    }
}

impl From<parser::Literal> for Value {
    fn from(value: parser::Literal) -> Self {
        match value {
            parser::Literal::Int(val) => Self::Int(val),
        }
    }
}

#[derive(Clone, Copy)]
pub struct FunctionRef(usize);

impl Deref for FunctionRef {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

enum Operation {
    Push(Value),
    Call(FunctionRef),
}

impl Operation {
    fn execute(&self, runtime: &mut Runtime) -> Result<(), RuntimeError> {
        match self {
            Self::Push(val) => runtime.push(val.clone()),
            Self::Call(fn_ref) => runtime.call(*fn_ref)?,
        }
        Ok(())
    }
}

struct Block {
    ops: Vec<Operation>,
}

impl Block {
    fn execute(&self, runtime: &mut Runtime) -> Result<(), RuntimeError> {
        for op in &self.ops {
            op.execute(runtime)?;
        }
        Ok(())
    }

    fn from_items(
        items: Vec<parser::Item>,
        function_names: &HashMap<String, FunctionRef>,
    ) -> Result<Self, CompilationError> {
        let mut ops = vec![];
        for item in items {
            ops.push(match item {
                parser::Item::Literal(literal) => Operation::Push(literal.into()),
                parser::Item::Function(function) => {
                    let fn_ref = function_names
                        .get(&*function)
                        .ok_or_else(|| CompilationError::UnknownFunction(function.to_string()))?;
                    Operation::Call(*fn_ref)
                }
            });
        }
        Ok(Block { ops })
    }
}

type Function = Rc<dyn for<'a> Fn(&'a mut Runtime) -> Result<(), RuntimeError> + 'static>;

pub struct Runtime {
    function_names: HashMap<String, FunctionRef>,
    functions: Vec<Function>,
    stack: Vec<Value>,
}

impl Runtime {
    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn call(&mut self, function_ref: FunctionRef) -> Result<(), RuntimeError> {
        let function = Rc::clone(&self.functions[*function_ref]);
        function(self)
    }

    pub fn call_by_name(&mut self, name: &str) -> Result<(), CompilationError> {
        let Some(fn_id) = self.function_names.get(name) else {
            return Err(CompilationError::UnknownFunction(name.into()));
        };
        self.call(*fn_id);
        Ok(())
    }
}

#[derive(Default)]
pub struct RuntimeBuilder {
    function_names: HashMap<String, FunctionRef>,
    functions: Vec<Option<Function>>,
}

macro_rules! register_arithmetic_operator {
    ($self:ident, $symbol:tt, $ty:ident) => {
        $self.register_builtin_function(stringify!($symbol).into(), |runtime| {
            let b = runtime.pop();
            let a = runtime.pop();
            let result = match (a, b) {
                (Value::Int(a), Value::Int(b)) => a $symbol b,

            };
            runtime.push(Value::Int(result as i64));
        });

    }
}

impl RuntimeBuilder {
    pub fn populate_from_ast(&mut self, ast: parser::Program) -> Result<(), CompilationError> {
        let funcs: Vec<_> = ast
            .functions
            .into_iter()
            .map(|f| {
                let id = self.declare_function(f.name);
                (id, f.body)
            })
            .collect();
        for (id, body) in funcs {
            self.define_function(id, body)?;
        }
        Ok(())
    }

    pub fn declare_function(&mut self, name: String) -> FunctionRef {
        let id = FunctionRef(self.functions.len());
        self.function_names.insert(name, id);
        self.functions.push(None);
        id
    }

    pub fn define_function(
        &mut self,
        id: FunctionRef,
        body: Vec<parser::Item>,
    ) -> Result<(), CompilationError> {
        let block = Block::from_items(body, &self.function_names)?;
        self.functions[*id] = Some(Rc::new(move |runtime| block.execute(runtime)));
        Ok(())
    }

    pub fn register_builtin_function(
        &mut self,
        name: String,
        body: impl for<'a> Fn(&'a mut Runtime) -> Result<(), RuntimeError> + 'static,
    ) {
        let id = self.declare_function(name);
        self.functions[*id] = Some(Rc::new(body));
    }

    pub fn register_default_builtins(&mut self) {
        self.register_builtin_function("print".into(), |runtime| {
            let value = runtime.pop();
            println!("{value}");
            Ok(())
        });
        self.register_builtin_function("input".into(), |runtime| {
            let mut stdin = std::io::stdin().lock();
            let mut buf = String::new();
            stdin.read_line(&mut buf).unwrap();
            let num: i64 = buf.trim().parse().unwrap();
            runtime.push(Value::Int(num));
        });
        self.register_builtin_function("swap".into(), |runtime| {
            let b = runtime.pop();
            let a = runtime.pop();
            runtime.push(b);
            runtime.push(a);
        });
        self.register_builtin_function("dig".into(), |runtime| {
            let Value::Int(n) = runtime.pop();
            let n = runtime.stack.len() - n as usize;
            let val = runtime.stack.remove(n);
            runtime.stack.push(val);
        });
        self.register_builtin_function("pop".into(), |runtime| {
            runtime.pop();
        });
        register_arithmetic_operator!(self, +);
        register_arithmetic_operator!(self, -);
        register_arithmetic_operator!(self, *);
        register_arithmetic_operator!(self, /);
        register_arithmetic_operator!(self, ==);
    }

    pub fn build(self) -> Result<Runtime, CompilationError> {
        let mut functions = vec![];
        for (id, function) in self.functions.into_iter().enumerate() {
            match function {
                Some(f) => functions.push(f),
                None => {
                    let missing_func_name =
                        self.function_names.iter().find(|f| **f.1 == id).unwrap().0;
                    return Err(CompilationError::UnknownFunction(missing_func_name.into()));
                }
            }
        }

        Ok(Runtime {
            functions,
            function_names: self.function_names,
            stack: vec![],
        })
    }
}
