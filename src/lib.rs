pub mod func;

use std::collections::HashMap;

use func::FuncTranspiler;
use sonatina_ir::{
    builder::ModuleBuilder,
    global_variable::GvInitializer,
    isa::evm::Evm,
    module::{FuncRef, ModuleCtx},
    GlobalVariable, GlobalVariableData, Linkage, Module, Signature, Type, I256, U256,
};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
use yultsur::{
    yul::{
        self, Block as YulBlock, Data, FunctionDefinition, Identifier, IdentifierID, InnerRoot,
        Object, Statement,
    },
    yul_parser::parse_root,
};

const TRIPLE: TargetTriple = TargetTriple::new(
    Architecture::Evm,
    Vendor::Ethereum,
    OperatingSystem::Evm(EvmVersion::Cancun),
);

pub fn compile(src: &str) -> Result<Module, String> {
    let root = parse_root(src)?;
    let mut ctx = Ctx::new();

    match &root.inner {
        InnerRoot::Object(obj) => {
            ctx.compile_object(obj);
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

    fn make_prefixed_name(&self, name: &str) -> String {
        let prefix = self.prefix();

        if prefix.is_empty() {
            name.to_string()
        } else {
            format!("{prefix}::{name}")
        }
    }

    fn prefix(&self) -> String {
        match self {
            Self::Nested(scopes) => {
                let mut prefix = String::new();
                for s in scopes {
                    if !prefix.is_empty() {
                        prefix.push_str("::");
                    }
                    prefix.push_str(&s.prefix());
                }
                prefix
            }

            Self::Block(bn) => {
                format!("block{bn}")
            }

            Self::Func(name) | Self::Object(name) => name.clone(),

            Self::Root => String::new(),
        }
    }

    fn object(obj: &Object) -> Self {
        let name = strip_enclosing_quote(&obj.name);
        Self::Object(name.to_string())
    }
}

pub struct Ctx {
    funcs: Vec<HashMap<String, FuncRef>>,
    object_items: Vec<HashMap<String, ObjectItem>>,
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
            object_items: Vec::new(),
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

    fn lookup_item(&self, name: &str) -> Option<ObjectItem> {
        for scope in &self.object_items {
            if let Some(item) = scope.get(name) {
                return Some(*item);
            }
        }
        None
    }

    fn compile_object(&mut self, obj: &Object) -> FuncRef {
        self.scope.push(Scope::object(obj));
        self.object_items.push(HashMap::new());

        // Declare all data in this obejct as a global variable.
        for data in &obj.data {
            self.declare_global_var(data);
        }

        for inner_obj in &obj.objects {
            let fb = self.compile_object(inner_obj);
            self.object_items.last_mut().unwrap().insert(
                strip_enclosing_quote(&inner_obj.name).to_string(),
                ObjectItem::ContractCode(fb),
            );
        }

        // Lower the code section.
        // NOTE: Code section is just a normal function in sonatina.
        //
        // Make a dummy yul funciton for contract code.
        let name = Identifier {
            id: IdentifierID::UnresolvedReference,
            name: "__init__".to_string(),
            location: None,
        };
        let yul_func = FunctionDefinition {
            name,
            parameters: Vec::new(),
            returns: Vec::new(),
            body: obj.code.body.clone(),
            location: obj.code.location.clone(),
        };

        let func_ref = self.declare_function(&yul_func);
        self.object_items.last_mut().unwrap().insert(
            strip_enclosing_quote(&obj.name).to_string(),
            ObjectItem::ContractCode(func_ref),
        );

        // Transpile contract code.
        let fb = self.mb.func_builder(func_ref);
        FuncTranspiler::new(self, fb).build(&yul_func);

        self.object_items.pop();
        self.scope.pop();
        func_ref
    }

    fn enter_block(&mut self, yul_block: &YulBlock) {
        let mut func_defs: HashMap<FuncRef, &FunctionDefinition> = HashMap::new();
        self.scope.push(Scope::Block(self.block_number));
        self.funcs.push(HashMap::new());

        // Collect functions and blocks in this block.
        let mut blocks = Vec::new();
        for stmt in &yul_block.statements {
            match stmt {
                Statement::FunctionDefinition(yul_func) => {
                    let func_ref = self.declare_function(yul_func);
                    self.funcs
                        .last_mut()
                        .unwrap()
                        .insert(yul_func.name.name.clone(), func_ref);
                    func_defs.insert(func_ref, yul_func);
                }
                Statement::Block(block) => blocks.push(block),
                _ => {}
            }
        }

        self.block_number += 1;
        // Transpile yul functions in this block.
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

    fn declare_function(&mut self, yul_func: &FunctionDefinition) -> FuncRef {
        let sig = self.make_sig(yul_func);
        self.mb.declare_function(sig)
    }

    fn leave_block(&mut self) {
        self.scope.pop().unwrap();
        self.funcs.pop().unwrap();
    }

    fn make_sig(&mut self, func_def: &FunctionDefinition) -> Signature {
        let name = self.scope.make_prefixed_name(&func_def.name.name);
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

    fn declare_global_var(&mut self, data: &Data) -> GlobalVariable {
        let name = &data.name[1..data.name.len() - 1];
        let prefixed_name = self.scope.make_prefixed_name(name);
        let (data, ty) = self.parse_data_value(data);

        let gv_data = GlobalVariableData::constant(prefixed_name, ty, Linkage::Private, data);
        let gv = self.mb.make_global(gv_data);
        self.object_items
            .last_mut()
            .unwrap()
            .insert(name.to_string(), gv.into());
        gv
    }

    fn parse_data_value(&self, data: &Data) -> (GvInitializer, Type) {
        let data = &data.data;
        if data.starts_with("hex") {
            // The actual hex literal is surrounded by `"`, or `'`.
            let u256 = U256::from_str_radix(&data[4..data.len() - 1], 16).unwrap();
            let cv = GvInitializer::make_imm(I256::make_positive(u256));
            (cv, Type::I256)
        } else {
            let value: Vec<_> = data
                .bytes()
                .map(|b| GvInitializer::Immediate(b.into()))
                .collect();
            let len = value.len();
            let cv = GvInitializer::make_array(value);
            let ty = self.mb.declare_array_type(Type::I8, len);

            (cv, ty)
        }
    }
}

impl Default for Ctx {
    fn default() -> Self {
        Self::new()
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
                U256::from_str_radix(lit, 10).unwrap()
            }

            "true" => U256::one(),

            "false" => U256::zero(),

            lit => {
                return Self::String(strip_enclosing_quote(lit).to_string());
            }
        };

        Self::Number(I256::make_positive(u256))
    }

    pub fn as_imm(&self) -> I256 {
        let s = match self {
            Self::Number(num) => return *num,
            Self::String(s) => s,
        };

        let s = strip_enclosing_quote(s);
        let mut bytes: Vec<u8> = s.bytes().collect();
        let len = bytes.len();
        bytes.resize(32, 0);
        assert!(len <= 32);
        I256::from_be_bytes(&bytes)
    }
}

#[derive(Debug, Clone, Copy)]
enum ObjectItem {
    GlobalVariable(GlobalVariable),
    ContractCode(FuncRef),
}

impl From<GlobalVariable> for ObjectItem {
    fn from(value: GlobalVariable) -> Self {
        Self::GlobalVariable(value)
    }
}

impl From<FuncRef> for ObjectItem {
    fn from(value: FuncRef) -> Self {
        Self::ContractCode(value)
    }
}

fn strip_enclosing_quote(s: &str) -> &str {
    let len = s.len();
    &s[1..len - 1]
}
