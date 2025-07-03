use std::{
    collections::HashMap,
    fmt::Display,
    io::{BufRead, Write},
    ops::Deref,
    rc::Rc,
};

use thiserror::Error;

use crate::parser;

#[derive(Debug, Error)]
pub enum CompilationError {
    #[error("Unknown function name \"{0}\"")]
    UnknownFunction(String),

    #[error("Internal error: {0}")]
    Internal(String),
}

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("Tried to pop from an empty stack")]
    EmptyStack,

    #[error("Type error: {0}")]
    Type(String),

    #[error("Unknown function name \"{0}\"")]
    UnknownFunction(String),

    #[error("Tried accessing out-of-range stack offset {n}; stack size is {stack_size}")]
    OutOfStackRange { n: i64, stack_size: usize },

    #[error("{0}")]
    User(String),

    #[error(transparent)]
    Io(#[from] std::io::Error),
}

#[derive(Clone, Debug, PartialEq)]
enum Value {
    Int(i64),
    Bool(bool),
    String(String),
    Block(FunctionRef),
}

impl Value {
    fn get_type(&self) -> Type {
        match self {
            Value::Int(_) => Type::Int,
            Value::Bool(_) => Type::Bool,
            Value::String(_) => Type::String,
            Value::Block(_) => Type::Block,
        }
    }

    fn is_truthy(&self) -> bool {
        match self {
            Value::Int(val) => *val != 0,
            Value::Bool(val) => *val,
            Value::String(val) => !val.is_empty(),
            Value::Block(_) => true,
        }
    }

    fn is_falsy(&self) -> bool {
        !self.is_truthy()
    }
}

#[derive(Clone, Copy, Debug)]
enum Type {
    Int,
    Bool,
    String,
    Block,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "string"),
            Type::Block => write!(f, "block"),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(val) => write!(f, "{val}"),
            Value::Bool(val) => write!(f, "{val}"),
            Value::String(val) => write!(f, "{val}"),
            Value::Block(_) => write!(f, "<block>"),
        }
    }
}

impl From<parser::Literal> for Value {
    fn from(value: parser::Literal) -> Self {
        match value {
            parser::Literal::Int(val) => Self::Int(val),
            parser::Literal::String(val) => Self::String(val),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
            Self::Push(val) => {
                runtime.push(val.clone());
                Ok(())
            }
            Self::Call(fn_ref) => runtime.call(*fn_ref),
        }
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
        runtime_builder: &mut RuntimeBuilder,
    ) -> Result<Self, CompilationError> {
        let mut ops = vec![];
        for item in items {
            ops.push(match item {
                parser::Item::Literal(literal) => Operation::Push(literal.into()),
                parser::Item::Function(function) => {
                    let fn_ref = runtime_builder
                        .function_names
                        .get(&*function)
                        .ok_or_else(|| CompilationError::UnknownFunction(function.to_string()))?;
                    Operation::Call(*fn_ref)
                }
                parser::Item::Block(block) => {
                    let fn_id = runtime_builder.define_anonymous_function(block)?;
                    Operation::Push(Value::Block(fn_id))
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

    fn pop(&mut self) -> Result<Value, RuntimeError> {
        let Some(val) = self.stack.pop() else {
            return Err(RuntimeError::EmptyStack);
        };
        Ok(val)
    }

    fn stack_offset_to_index(&self, n: i64) -> Option<usize> {
        let Ok(n_usize) = usize::try_from(n) else {
            return None;
        };
        self.size().checked_sub(n_usize + 1)
    }

    fn try_dig(&self, n: i64) -> Option<&Value> {
        let idx = self.stack_offset_to_index(n)?;
        self.stack.get(idx)
    }

    fn dig(&self, n: i64) -> Result<&Value, RuntimeError> {
        self.try_dig(n)
            .ok_or_else(|| RuntimeError::OutOfStackRange {
                n,
                stack_size: self.size(),
            })
    }

    fn bury(&mut self, n: i64, mut value: Value) -> Result<Value, RuntimeError> {
        let Some(idx) = self.stack_offset_to_index(n) else {
            return Err(RuntimeError::OutOfStackRange {
                n,
                stack_size: self.size(),
            });
        };
        std::mem::swap(&mut self.stack[idx], &mut value);
        Ok(value)
    }

    fn insert(&mut self, n: i64, value: Value) -> Result<(), RuntimeError> {
        let Some(idx) = self.stack_offset_to_index(n) else {
            return Err(RuntimeError::OutOfStackRange {
                n,
                stack_size: self.size(),
            });
        };
        self.stack.insert(idx.saturating_sub(1), value);
        Ok(())
    }

    fn top(&self, n: i64) -> Result<&[Value], RuntimeError> {
        let Some(idx) = self.stack_offset_to_index(n) else {
            return Err(RuntimeError::OutOfStackRange {
                n,
                stack_size: self.size(),
            });
        };
        Ok(&self.stack[idx..])
    }

    fn size(&self) -> usize {
        self.stack.len()
    }

    fn call(&mut self, function_ref: FunctionRef) -> Result<(), RuntimeError> {
        let function = Rc::clone(&self.functions[*function_ref]);
        function(self)
    }

    pub fn call_by_name(&mut self, name: &str) -> Result<(), RuntimeError> {
        let Some(fn_id) = self.function_names.get(name) else {
            return Err(RuntimeError::UnknownFunction(name.into()));
        };
        self.call(*fn_id)?;
        Ok(())
    }
}

#[derive(Default)]
pub struct RuntimeBuilder {
    function_names: HashMap<String, FunctionRef>,
    functions: Vec<Option<Function>>,
}

macro_rules! register_numeric_operator {
    ($self:ident, $symbol:tt, $typ:ident) => {
        $self.register_builtin_function(stringify!($symbol).into(), |runtime| {
            let b = runtime.pop()?;
            let a = runtime.pop()?;
            let result = match (&a, &b) {
                (Value::Int(a), Value::Int(b)) => a $symbol b,
                _ => return Err(RuntimeError::Type(format!("Numeric operations can only be performed on numbers; received {} and {}", a.get_type(), b.get_type())))

            };
            runtime.push(Value::$typ(result as _));
            Ok(())
        });
    }
}

macro_rules! register_boolean_operator {
    ($self:ident, $symbol:tt) => {
        $self.register_builtin_function(stringify!($symbol).into(), |runtime| {
            let b = runtime.pop()?;
            let a = runtime.pop()?;
            runtime.push(Value::Bool(b.is_truthy() $symbol a.is_truthy()));
            Ok(())
        });
    };
}

macro_rules! cast {
    ($val:expr, $ty:ident, $msg:literal $(, $arg:expr)*) => {
        {
            let value = $val;
            match value{
                Value::$ty(val) => Ok(val),
                _ => {
                    let formatted_msg = format_args!($msg, $($arg),*);
                    let full_msg = format!("{formatted_msg}; expected `{}` but received `{}`", Type::$ty, value.get_type());
                    Err(RuntimeError::Type(full_msg))
                }
            }
        }
    };
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
        let id = self.reserve_function_id();
        self.function_names.insert(name, id);
        id
    }

    pub fn define_anonymous_function(
        &mut self,
        body: parser::Block,
    ) -> Result<FunctionRef, CompilationError> {
        let id = self.reserve_function_id();
        self.define_function(id, body)?;
        Ok(id)
    }

    fn reserve_function_id(&mut self) -> FunctionRef {
        let id = self.functions.len();
        self.functions.push(None);
        FunctionRef(id)
    }

    pub fn define_function(
        &mut self,
        id: FunctionRef,
        body: parser::Block,
    ) -> Result<(), CompilationError> {
        let block = Block::from_items(body.0, self)?;
        self.functions[*id] = Some(Rc::new(move |runtime| {
            block.execute(runtime)?;
            Ok(())
        }));
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
        self.register_builtin_function("dbg".into(), |runtime| {
            println!("Current stack:\n{:?}", runtime.stack);
            Ok(())
        });
        self.register_builtin_function("error".into(), |runtime| {
            Err::<(), _>(RuntimeError::User(runtime.pop()?.to_string()))
        });
        self.register_builtin_function("print".into(), |runtime| {
            let value = runtime.pop()?;
            print!("{value}");
            Ok(())
        });
        self.register_builtin_function("println".into(), |runtime| {
            let value = runtime.pop()?;
            println!("{value}");
            Ok(())
        });
        self.register_builtin_function("input".into(), |runtime| {
            std::io::stdout().flush()?;
            let mut stdin = std::io::stdin().lock();
            let mut buf = String::new();
            stdin.read_line(&mut buf)?;
            runtime.push(Value::String(buf.trim().into()));
            Ok(())
        });
        self.register_builtin_function("swap".into(), |runtime| {
            let n = cast!(runtime.pop()?, Int, "Invalid first argument to `dig`")?;
            let top = runtime.pop()?;
            let bottom = runtime.bury(n, top)?;
            runtime.push(bottom);
            Ok(())
        });
        self.register_builtin_function("dig".into(), |runtime| {
            let n = cast!(runtime.pop()?, Int, "Invalid first argument to `dig`")?;
            let val = runtime.dig(n)?;
            runtime.push(val.clone());
            Ok(())
        });
        self.register_builtin_function("bury".into(), |runtime| {
            let n = cast!(runtime.pop()?, Int, "Invalid first argument to `bury`")?;
            let val = runtime.pop()?;
            runtime.bury(n, val)?;
            Ok(())
        });
        self.register_builtin_function("insert".into(), |runtime| {
            let n = cast!(runtime.pop()?, Int, "Invalid first argument to `bury`")?;
            let val = runtime.pop()?;
            runtime.insert(n, val)?;
            Ok(())
        });
        self.register_builtin_function("top".into(), |runtime| {
            let n = cast!(runtime.pop()?, Int, "Invalid first argumetn to `clone`")?;
            let top = runtime.top(n)?.to_vec();
            for val in top {
                runtime.push(val);
            }
            Ok(())
        });
        self.register_builtin_function("pop".into(), |runtime| {
            runtime.pop()?;
            Ok(())
        });
        self.register_builtin_function("=".into(), |runtime| {
            let a = runtime.pop()?;
            let b = runtime.pop()?;
            runtime.push(Value::Bool(a == b));
            Ok(())
        });
        self.register_builtin_function("!=".into(), |runtime| {
            let a = runtime.pop()?;
            let b = runtime.pop()?;
            runtime.push(Value::Bool(a != b));
            Ok(())
        });
        self.register_builtin_function("!".into(), |runtime| {
            let a = runtime.pop()?;
            runtime.push(Value::Bool(a.is_falsy()));
            Ok(())
        });
        self.register_builtin_function("call".into(), |runtime| {
            let fn_ref = cast!(runtime.pop()?, Block, "Invalid argument to `call`")?;
            runtime.call(fn_ref)?;
            Ok(())
        });
        self.register_builtin_function("if".into(), |runtime| {
            let pred_block = cast!(runtime.pop()?, Block, "Invalid second argument to `if`")?;
            let body_block = cast!(runtime.pop()?, Block, "Invalid first argument to `if`")?;
            runtime.call(pred_block)?;
            if runtime.pop()?.is_truthy() {
                runtime.call(body_block)?;
            }
            Ok(())
        });
        self.register_builtin_function("if_else".into(), |runtime| {
            let pred_block = cast!(runtime.pop()?, Block, "Invalid third argument to `if_else`")?;
            let else_block = cast!(
                runtime.pop()?,
                Block,
                "Invalid second argument to `if_else`"
            )?;
            let if_block = cast!(runtime.pop()?, Block, "Invalid first argument to `if_else`")?;
            runtime.call(pred_block)?;
            if runtime.pop()?.is_truthy() {
                runtime.call(if_block)?;
            } else {
                runtime.call(else_block)?;
            }
            Ok(())
        });
        self.register_builtin_function("while".into(), |runtime| {
            let pred_block = cast!(runtime.pop()?, Block, "Invalid second argument to `while`")?;
            let body_block = cast!(runtime.pop()?, Block, "Invalid first argument to `while`")?;

            loop {
                runtime.call(pred_block)?;
                if runtime.pop()?.is_falsy() {
                    break;
                }
                runtime.call(body_block)?;
            }

            Ok(())
        });
        self.register_builtin_function("^".into(), |runtime| {
            let val = runtime.pop()?;
            runtime.push(val.clone());
            runtime.push(val);
            Ok(())
        });
        register_numeric_operator!(self, +, Int);
        register_numeric_operator!(self, -, Int);
        register_numeric_operator!(self, *, Int);
        register_numeric_operator!(self, /, Int);
        register_numeric_operator!(self, <<, Int);
        register_numeric_operator!(self, >>, Int);
        register_numeric_operator!(self, &, Int);
        register_numeric_operator!(self, |, Int);
        register_numeric_operator!(self, %, Int);
        register_numeric_operator!(self, <, Bool);
        register_numeric_operator!(self, >, Bool);
        register_numeric_operator!(self, <=, Bool);
        register_numeric_operator!(self, >=, Bool);
        register_boolean_operator!(self, &&);
        register_boolean_operator!(self, ||);
    }

    pub fn build(self) -> Result<Runtime, CompilationError> {
        let mut functions = vec![];
        for (id, function) in self.functions.iter().enumerate() {
            match function {
                Some(f) => functions.push(f.clone()),
                None => {
                    let missing_func_name = self
                        .function_names
                        .iter()
                        .find_map(|(name, fn_ref)| (**fn_ref == id).then_some(name));
                    match missing_func_name {
                        Some(name) => return Err(CompilationError::UnknownFunction(name.into())),
                        None => {
                            return Err(CompilationError::Internal(format!(
                                "Anonymous function {id} wasn't populated"
                            )));
                        }
                    }
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
