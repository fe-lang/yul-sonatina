pub mod func;

use std::collections::HashMap;

use func::FuncTranspiler;
use sonatina_ir::{
    builder::ModuleBuilder,
    isa::evm::Evm,
    module::{FuncRef, ModuleCtx},
    Linkage, Module, Signature, Type, I256, U256,
};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
use yultsur::{
    yul::{self, Block as YulBlock, FunctionDefinition, InnerRoot, Statement},
    yul_parser::parse_root,
};

const TRIPLE: TargetTriple = TargetTriple::new(
    Architecture::Evm,
    Vendor::Ethereum,
    OperatingSystem::Evm(EvmVersion::London),
);

pub fn compile(src: &str) -> Result<Module, String> {
    let root = parse_root(src)?;
    let mut ctx = Ctx::new();

    match &root.inner {
        InnerRoot::Object(_) => {
            todo!()
        }
        InnerRoot::Block(yul_block) => ctx.enter_block(yul_block),
    };

    Ok(ctx.finish())
}

#[derive(Debug, Clone)]
pub enum Scope {
    Nested(Vec<Scope>),
    Block(usize),
    Func(String),
    Object(String),
    Root,
}

impl Scope {
    fn pop(&mut self) -> Option<Scope> {
        match self {
            Self::Nested(v) => v.pop(),
            _ => None,
        }
    }

    fn push(&mut self, scope: Scope) {
        assert!(!matches!(scope, Scope::Nested(_)));
        match self {
            Self::Nested(n) => n.push(scope),
            _ => *self = Self::Nested(vec![self.clone(), scope]),
        }
    }

    fn make_func_name(&self, func_name: &str) -> String {
        let prefix = self.func_prefix();

        if prefix.is_empty() {
            func_name.to_string()
        } else {
            format!("{prefix}::{func_name}")
        }
    }

    fn func_prefix(&self) -> String {
        match self {
            Self::Nested(scopes) => {
                let mut prefix = String::new();
                for s in scopes {
                    if !prefix.is_empty() {
                        prefix.push_str("::");
                    }
                    prefix.push_str(&s.func_prefix());
                }
                prefix
            }

            Self::Block(bn) => {
                format!("yul_block{bn}")
            }

            Self::Func(name) | Self::Object(name) => name.clone(),

            Self::Root => String::new(),
        }
    }
}

pub struct Ctx {
    funcs: Vec<HashMap<String, FuncRef>>,
    scope: Scope,
    block_number: usize,
    mb: ModuleBuilder,
    declared_ret_tys: HashMap<usize, Type>,
}

impl Ctx {
    pub fn new() -> Self {
        let module_ctx = ModuleCtx::new(&Evm::new(TRIPLE));
        let mb = ModuleBuilder::new(module_ctx);
        Self {
            funcs: Vec::new(),
            scope: Scope::Root,
            block_number: 0,
            mb,
            declared_ret_tys: HashMap::new(),
        }
    }

    pub fn finish(self) -> Module {
        self.mb.build()
    }

    fn lookup_func(&self, name: &str) -> Option<FuncRef> {
        for scope in self.funcs.iter().rev() {
            if let Some(func) = scope.get(name) {
                return Some(*func);
            }
        }
        None
    }

    fn enter_block(&mut self, yul_block: &YulBlock) {
        let mut funcs_in_scope = HashMap::new();
        let mut func_defs: HashMap<FuncRef, &FunctionDefinition> = HashMap::new();

        // Collect functions and blocks in this block.
        let mut blocks = Vec::new();
        for stmt in &yul_block.statements {
            match stmt {
                Statement::FunctionDefinition(yul_func) => {
                    let sig = self.make_sig(yul_func);
                    let func_ref = self.mb.declare_function(sig);
                    func_defs.insert(func_ref, yul_func);
                    funcs_in_scope.insert(yul_func.name.name.clone(), func_ref);
                }
                Statement::Block(block) => blocks.push(block),
                _ => {}
            }
        }

        self.scope.push(Scope::Block(self.block_number));
        self.funcs.push(funcs_in_scope);
        self.block_number += 1;

        // Transpile all yul functions into sonatina functions.
        for (func_ref, yul_func) in func_defs {
            let fb = self.mb.func_builder(func_ref);
            FuncTranspiler::new(self, fb).build(yul_func);
        }

        // Search and transpile functions in the child blocks.
        for block in blocks {
            self.enter_block(block);
            self.leave_block();
        }
    }

    fn make_sig(&mut self, func_def: &FunctionDefinition) -> Signature {
        let name = self.scope.make_func_name(&func_def.name.name);
        let args = vec![Type::I256; func_def.parameters.len()];
        let ret_ty = self.declare_ret_ty(func_def.returns.len());
        Signature::new(&name, Linkage::Private, &args, ret_ty)
    }

    fn declare_ret_ty(&mut self, n_ret: usize) -> Type {
        if let Some(ty) = self.declared_ret_tys.get(&n_ret) {
            return *ty;
        }

        let ret_ty = if n_ret == 0 {
            Type::Unit
        } else if n_ret == 1 {
            Type::I256
        } else {
            let type_name = format!("tuple{n_ret}");
            let fields = vec![Type::I256; n_ret];
            self.mb.declare_struct_type(&type_name, &fields, false)
        };

        self.declared_ret_tys.insert(n_ret, ret_ty);
        ret_ty
    }

    fn leave_block(&mut self) {
        self.scope.pop().unwrap();
        self.funcs.pop().unwrap();
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
