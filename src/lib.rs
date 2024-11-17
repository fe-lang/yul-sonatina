pub mod func;

use std::collections::HashMap;

use sonatina_ir::{module::FuncRef, Module, I256, U256};
use yultsur::yul;

pub fn compile(src: &str) -> Module {
    todo!()
}

pub enum Scope {
    Nested(Vec<Scope>),
    Block(usize),
    Func(FuncRef),
    Object(String),
}

pub struct Ctx {
    funcs: Vec<HashMap<String, FuncRef>>,
    scope: Scope,
}

impl Ctx {
    pub fn lookup_func(&self, name: &str) -> Option<FuncRef> {
        for scope in self.funcs.iter().rev() {
            if let Some(func) = scope.get(name) {
                return Some(*func);
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Number(I256),
    String(String),
}

impl Literal {
    pub fn parse(yul_lit: &yul::Literal) -> Self {
        let u256 = match yul_lit.literal.as_str() {
            lit if lit.starts_with("0x") => U256::from_str_radix(&lit[2..], 16).unwrap(),

            lit if lit.chars().next().unwrap().is_numeric() => {
                U256::from_str_radix(&lit, 10).unwrap()
            }

            "true" => U256::one(),

            "false" => U256::zero(),

            lit => {
                assert!(lit.starts_with("\""));
                let last = lit.len();
                return Self::String((&lit[1..last - 1]).to_string());
            }
        };

        Self::Number(I256::make_positive(u256))
    }

    pub fn as_i256(&self) -> Option<I256> {
        let _s = match self {
            Self::Number(num) => return Some(*num),
            Self::String(s) => s,
        };

        todo!()
    }
}
