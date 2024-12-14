use std::collections::HashMap;

use sonatina_ir::{
    builder::FunctionBuilder,
    func_cursor::InstInserter,
    inst::{arith::*, cast::*, cmp::*, control_flow::*, data::*, evm::*, logic::*},
    BlockId, Inst, Type, ValueId, Variable, I256,
};
use yultsur::yul::{
    Block as YulBlock, Expression, FunctionCall, FunctionDefinition, Identifier,
    Literal as YulLiteral, Statement,
};

use crate::{Ctx, Literal, ObjectItem};

pub struct FuncTranspiler<'ctx> {
    ctx: &'ctx mut Ctx,
    func_ctx: FuncCtx,
    builder: FunctionBuilder<InstInserter>,
    ret_vars: Vec<String>,
}

impl<'ctx> FuncTranspiler<'ctx> {
    pub fn new(ctx: &'ctx mut Ctx, builder: FunctionBuilder<InstInserter>) -> Self {
        Self {
            ctx,
            func_ctx: FuncCtx::new(),
            builder,
            ret_vars: Vec::new(),
        }
    }

    pub fn build(mut self, yul_func: &FunctionDefinition) {
        for arg in &yul_func.parameters {
            self.func_ctx.declare_var(&mut self.builder, &arg.name);
        }

        for ret in &yul_func.returns {
            self.ret_vars.push(ret.name.clone());
            self.func_ctx.declare_var(&mut self.builder, &ret.name);
        }

        let entry_bb = self.builder.append_block();
        self.builder.switch_to_block(entry_bb);

        for (i, yul_var) in yul_func.parameters.iter().enumerate() {
            let yul_var = self.func_ctx.lookup_var(&yul_var.name);
            let arg_val = self.builder.args()[i];
            self.builder.def_var(yul_var, arg_val);
        }

        self.block(&yul_func.body, true, None);
        self.builder.seal_all();
        self.builder.finish();
    }

    /// Returns `true` if the statement is the terminator.
    fn stmt(&mut self, yul_stmt: &Statement) {
        let inst_set = self.builder.inst_set();

        match yul_stmt {
            Statement::Block(block) => self.block(block, true, None),

            Statement::FunctionDefinition(_) => {
                // We can just ignore function definitions.
                // Function definitions are handled by the context.
            }

            Statement::VariableDeclaration(yul_decl) => {
                let yul_vars = &yul_decl.variables;
                for yul_var in yul_vars {
                    self.func_ctx.declare_var(&mut self.builder, &yul_var.name);
                }

                let Some(expr) = &yul_decl.value else {
                    return;
                };
                let value = self.expr(expr).unwrap();
                self.func_ctx.def_var(&mut self.builder, yul_vars, value);
            }

            Statement::Assignment(assign) => {
                let value = self.expr(&assign.value).unwrap();
                self.func_ctx
                    .def_var(&mut self.builder, &assign.variables, value);
            }

            Statement::Expression(expr) => {
                self.expr(expr);
                let last_inst = self.builder.last_inst().unwrap();
                if self.builder.is_terminator(last_inst) {
                    self.builder.seal_block();
                }
            }

            Statement::If(if_) => {
                let then_bb = self.builder.append_block();
                let merge_bb = self.builder.append_block();

                let cond = self.expr(&if_.condition).unwrap();
                let br = Br::new_unchecked(inst_set, cond, then_bb, merge_bb);
                self.builder.insert_inst_no_result(br);

                // Enter then block.
                self.builder.switch_to_block(then_bb);
                self.block(&if_.body, true, Some(merge_bb));

                // Switch to merge block.
                self.builder.switch_to_block(merge_bb);
            }

            Statement::Switch(switch) => {
                let scrutinee = self.expr(&switch.expression).unwrap();

                // Collect cases.
                let labeled: Vec<(ValueId, BlockId, &YulBlock)> = switch
                    .cases
                    .iter()
                    .flat_map(|case| {
                        let yul_lit = case.literal.as_ref()?;
                        let lit_value = self.lit(yul_lit);
                        let bb = self.builder.append_block();
                        Some((lit_value, bb, &case.body))
                    })
                    .collect();
                let default = switch.cases.iter().find_map(|case| {
                    if case.literal.is_some() {
                        return None;
                    }
                    let bb = self.builder.append_block();
                    Some((bb, &case.body))
                });

                // Make and append `br_table` inst.
                let merge_bb = self.builder.append_block();

                let table = labeled.iter().map(|(value, bb, _)| (*value, *bb)).collect();
                let br_inst = if let Some((default, _)) = default {
                    BrTable::new_unchecked(inst_set, scrutinee, Some(default), table)
                } else {
                    BrTable::new_unchecked(inst_set, scrutinee, Some(merge_bb), table)
                };
                self.builder.insert_inst_no_result(br_inst);
                self.builder.seal_block();

                // Transpile cases.
                for (_, bb, yul_block) in labeled {
                    self.builder.switch_to_block(bb);
                    self.block(yul_block, true, Some(merge_bb));
                }
                if let Some((bb, yul_block)) = default {
                    self.builder.switch_to_block(bb);
                    self.block(yul_block, true, Some(merge_bb));
                }

                self.builder.switch_to_block(merge_bb);
            }

            Statement::ForLoop(for_) => {
                let lp_header = self.builder.append_block();
                let lp_body = self.builder.append_block();
                let lp_post = self.builder.append_block();
                let lp_exit = self.builder.append_block();

                // Lower pre block.
                // Yul's scoping rule about `for` loop is weird.
                // See https://docs.soliditylang.org/en/latest/yul.html#scoping-rules
                self.enter_scope(&for_.pre);
                self.block(&for_.pre, false, Some(lp_header));

                // Lower loop header.
                self.builder.switch_to_block(lp_header);
                let cond = self.expr(&for_.condition).unwrap();
                let br = Br::new_unchecked(inst_set, cond, lp_body, lp_exit);
                self.builder.insert_inst_no_result(br);

                // Lower loop body.
                self.func_ctx.loop_stack.push((lp_post, lp_exit));
                self.builder.switch_to_block(lp_body);
                self.block(&for_.body, true, Some(lp_post));
                self.func_ctx.loop_stack.pop();

                // Lower loop post block.
                self.builder.switch_to_block(lp_post);
                self.block(&for_.post, true, Some(lp_header));

                // Leave loop scope.
                self.builder.switch_to_block(lp_header);
                self.builder.seal_block();
                self.leave_scope();

                self.builder.switch_to_block(lp_exit);
            }

            Statement::Break => {
                let break_dest = self.func_ctx.loop_stack.last().unwrap().1;
                let jump = Jump::new_unchecked(inst_set, break_dest);
                self.builder.insert_inst_no_result(jump);
                self.builder.seal_block();
            }

            Statement::Continue => {
                let break_dest = self.func_ctx.loop_stack.last().unwrap().0;
                let jump = Jump::new_unchecked(inst_set, break_dest);
                self.builder.insert_inst_no_result(jump);
                self.builder.seal_block();
            }

            Statement::Leave => self.insert_return(),
        }
    }

    fn enter_scope(&mut self, yul_block: &YulBlock) {
        self.ctx.enter_block(yul_block);
        self.func_ctx.variables.push(HashMap::default());
    }

    fn leave_scope(&mut self) {
        self.func_ctx.variables.pop().unwrap();
        self.ctx.leave_block();
    }

    fn block(&mut self, yul_block: &YulBlock, enter_scope: bool, fallback_to: Option<BlockId>) {
        if enter_scope {
            self.enter_scope(yul_block);
        }

        for yul_stmt in &yul_block.statements {
            self.stmt(yul_stmt);
            let current_bb = self.builder.current_block().unwrap();
            if self.builder.is_sealed(current_bb) {
                self.ctx.leave_block();
                return;
            }
        }

        let current_bb = self.builder.current_block().unwrap();
        if !self.builder.is_sealed(current_bb) {
            self.builder.switch_to_block(current_bb);
            match fallback_to {
                Some(bb) => {
                    let inst_set = self.builder.inst_set();
                    let jump = Jump::new_unchecked(inst_set, bb);
                    self.builder.insert_inst_no_result(jump);
                }
                None => {
                    self.insert_return();
                }
            }

            self.builder.seal_block();
        }

        if enter_scope {
            self.leave_scope();
        }
    }

    fn insert_return(&mut self) {
        let inst_set = self.builder.inst_set();

        let ret_val = match self.ret_vars.len() {
            0 => None,
            1 => {
                let var = self.func_ctx.lookup_var(&self.ret_vars[0]);
                Some(self.builder.use_var(var))
            }
            _ => {
                let func_ref = self.builder.func_ref;
                let ret_ty = self
                    .builder
                    .module_builder
                    .ctx
                    .func_sig(func_ref, |sig| sig.ret_ty());
                let mut ret_val = self.builder.make_undef_value(ret_ty);
                for (i, yul_var) in self.ret_vars.iter().enumerate() {
                    let var = self.func_ctx.lookup_var(yul_var);
                    let elem = self.builder.use_var(var);
                    let idx = self.builder.make_imm_value(I256::from_usize(i));
                    let insert_value = InsertValue::new_unchecked(inst_set, ret_val, idx, elem);
                    ret_val = self.builder.insert_inst(insert_value, ret_ty);
                }

                Some(ret_val)
            }
        };

        let ret_inst = Return::new_unchecked(inst_set, ret_val);
        self.builder.insert_inst_no_result(ret_inst);
        self.builder.seal_block();
    }

    fn expr(&mut self, yul_expr: &Expression) -> Option<ValueId> {
        match yul_expr {
            Expression::Literal(lit) => Some(self.lit(lit)),
            Expression::Identifier(ident) => {
                let var = self.func_ctx.lookup_var(&ident.name);
                Some(self.builder.use_var(var))
            }
            Expression::FunctionCall(call) => self.func_call(call),
        }
    }

    fn lit(&mut self, yul_lit: &YulLiteral) -> ValueId {
        let lit = Literal::parse(yul_lit).as_imm();
        self.builder.make_imm_value(lit)
    }

    fn func_call(&mut self, yul_func_call: &FunctionCall) -> Option<ValueId> {
        let callee_name = yul_func_call.function.name.as_str();
        let m_ctx = self.builder.ctx();
        let inst_set = self.builder.ctx().inst_set;

        match callee_name {
            "dataoffset" => {
                let arg = &yul_func_call.arguments[0];
                let Literal::String(symbol) = (match arg {
                    Expression::Literal(yul_lit) => Literal::parse(yul_lit),
                    _ => unreachable!(),
                }) else {
                    unreachable!()
                };

                let item = self.ctx.lookup_item(&symbol).unwrap();
                let ptr = match item {
                    ObjectItem::ContractCode(func_ref) => {
                        let gfp = GetFunctionPtr::new_unchecked(inst_set, func_ref);
                        self.builder
                            .insert_inst(gfp, func_ref.as_ptr_ty(self.builder.ctx()))
                    }

                    ObjectItem::GlobalVariable(variable) => {
                        self.builder.make_global_value(variable)
                    }
                };

                return Some(self.ptoi(ptr));
            }

            "datasize" => {
                let arg = &yul_func_call.arguments[0];
                let Literal::String(symbol) = (match arg {
                    Expression::Literal(yul_lit) => Literal::parse(yul_lit),
                    _ => unreachable!(),
                }) else {
                    unreachable!()
                };
                let item = self.ctx.lookup_item(&symbol).unwrap();

                match item {
                    ObjectItem::ContractCode(func_ref) => {
                        let contract_size = EvmContractSize::new_unchecked(inst_set, func_ref);
                        return Some(self.builder.insert_inst(contract_size, Type::I256));
                    }

                    ObjectItem::GlobalVariable(variable) => {
                        let ty = variable.ty(self.builder.ctx());
                        let size = m_ctx.type_layout.size_of(ty, m_ctx).unwrap();
                        let value = self.builder.make_imm_value(I256::from_usize(size));
                        return Some(value);
                    }
                }
            }

            // Fallback to normal instruction call handling.
            _ => {}
        };

        let args: Vec<_> = yul_func_call
            .arguments
            .iter()
            .map(|expr| self.expr(expr).unwrap())
            .collect();

        let (inst, has_ret): (Box<dyn Inst>, _) = match callee_name {
            "stop" => (Box::new(EvmStop::new_unchecked(inst_set)), false),

            "add" => (
                Box::new(Add::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "sub" => (
                Box::new(Sub::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "mul" => (
                Box::new(Mul::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "div" => (
                Box::new(EvmUdiv::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "sdiv" => (
                Box::new(EvmSdiv::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "mod" => (
                Box::new(EvmUmod::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "smod" => (
                Box::new(EvmSmod::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "exp" => (
                Box::new(EvmExp::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "not" => (Box::new(Not::new_unchecked(inst_set, args[0])), true),
            "lt" => (
                Box::new(Lt::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "gt" => (
                Box::new(Gt::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "slt" => (
                Box::new(Slt::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "sgt" => (
                Box::new(Sgt::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "eq" => (
                Box::new(Eq::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "iszero" => (Box::new(IsZero::new_unchecked(inst_set, args[0])), true),
            "and" => (
                Box::new(And::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "or" => (
                Box::new(Or::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "byte" => (
                Box::new(EvmByte::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "shl" => (
                Box::new(Shl::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "shr" => (
                Box::new(Shr::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "sar" => (
                Box::new(Sar::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "addmod" => (
                Box::new(EvmAddMod::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                true,
            ),
            "mulmod" => (
                Box::new(EvmMulMod::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                true,
            ),
            "signextend" => todo!("Add EvmSignExtend?"),
            "keccak256" => (
                Box::new(EvmKeccak256::new_unchecked(inst_set, args[0], args[1])),
                true,
            ),
            "pop" => return None,
            "mload" => {
                let ptr = self.itop(args[0]);
                (
                    Box::new(Mload::new_unchecked(inst_set, ptr, Type::I256)),
                    true,
                )
            }
            "mstore" => {
                let ptr = self.itop(args[0]);
                (
                    Box::new(Mstore::new_unchecked(inst_set, ptr, args[1], Type::I256)),
                    false,
                )
            }
            "mstore8" => (
                Box::new(EvmMstore8::new_unchecked(inst_set, args[0], args[1])),
                false,
            ),
            "sload" => (Box::new(EvmSload::new_unchecked(inst_set, args[0])), true),
            "sstore" => (
                Box::new(EvmSstore::new_unchecked(inst_set, args[0], args[1])),
                false,
            ),
            "msize" => (Box::new(EvmMsize::new_unchecked(inst_set)), true),
            "gas" => (Box::new(EvmGas::new_unchecked(inst_set)), true),
            "address" => (Box::new(EvmGas::new_unchecked(inst_set)), true),
            "balance" => (Box::new(EvmBalance::new_unchecked(inst_set, args[0])), true),
            "selfbalance" => (Box::new(EvmSelfBalance::new_unchecked(inst_set)), true),
            "caller" => (Box::new(EvmCaller::new_unchecked(inst_set)), true),
            "callvalue" => (Box::new(EvmCallValue::new_unchecked(inst_set)), true),
            "calldataload" => (
                Box::new(EvmCalldataLoad::new_unchecked(inst_set, args[0])),
                true,
            ),
            "calldatasize" => (Box::new(EvmCalldataSize::new_unchecked(inst_set)), true),
            "calldatacopy" => (
                Box::new(EvmCalldataCopy::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                false,
            ),
            "codesize" => (Box::new(EvmCodeSize::new_unchecked(inst_set)), true),
            "codecopy" => (
                Box::new(EvmCodeCopy::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                false,
            ),
            "extcodesize" => (
                Box::new(EvmExtCodeSize::new_unchecked(inst_set, args[0])),
                true,
            ),
            "extcodecopy" => (
                Box::new(EvmExtCodeCopy::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3],
                )),
                false,
            ),
            "returndatasize" => (Box::new(EvmReturnDataSize::new_unchecked(inst_set)), true),
            "returndatacopy" => (
                Box::new(EvmReturnDataCopy::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                false,
            ),
            "mcopy" => (
                Box::new(EvmMcopy::new_unchecked(inst_set, args[0], args[1], args[2])),
                false,
            ),
            "extcodehash" => (
                Box::new(EvmExtCodeHash::new_unchecked(inst_set, args[0])),
                true,
            ),
            "create" => (
                Box::new(EvmCreate::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                true,
            ),
            "create2" => (
                Box::new(EvmCreate2::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3],
                )),
                true,
            ),
            "call" => (
                Box::new(EvmCall::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3], args[4], args[5], args[6],
                )),
                true,
            ),
            "callcode" => (
                Box::new(EvmCallCode::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3], args[4], args[5], args[6],
                )),
                true,
            ),
            "delegatecall" => (
                Box::new(EvmDelegateCall::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3], args[4], args[5],
                )),
                true,
            ),
            "staticcall" => (
                Box::new(EvmStaticCall::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3], args[4], args[5],
                )),
                true,
            ),
            "return" => (
                Box::new(EvmReturn::new_unchecked(inst_set, args[0], args[1])),
                false,
            ),
            "revert" => (
                Box::new(EvmRevert::new_unchecked(inst_set, args[0], args[1])),
                false,
            ),
            "selfdestruct" => (
                Box::new(EvmSelfDestruct::new_unchecked(inst_set, args[0])),
                false,
            ),
            "invalid" => (Box::new(EvmInvalid::new_unchecked(inst_set)), false),
            "log0" => (
                Box::new(EvmLog0::new_unchecked(inst_set, args[0], args[1])),
                false,
            ),
            "log1" => (
                Box::new(EvmLog1::new_unchecked(inst_set, args[0], args[1], args[2])),
                false,
            ),
            "log2" => (
                Box::new(EvmLog2::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3],
                )),
                false,
            ),
            "log3" => (
                Box::new(EvmLog3::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3], args[4],
                )),
                false,
            ),
            "log4" => (
                Box::new(EvmLog4::new_unchecked(
                    inst_set, args[0], args[1], args[2], args[3], args[4], args[5],
                )),
                false,
            ),
            "chainid" => (Box::new(EvmChainId::new_unchecked(inst_set)), true),
            "basefee" => (Box::new(EvmBaseFee::new_unchecked(inst_set)), true),
            "blobbasefee" => (Box::new(EvmBlobBaseFee::new_unchecked(inst_set)), true),
            "origin" => (Box::new(EvmOrigin::new_unchecked(inst_set)), true),
            "gasprice" => (Box::new(EvmGasPrice::new_unchecked(inst_set)), true),
            "blobhash" => (
                Box::new(EvmBlockHash::new_unchecked(inst_set, args[0])),
                true,
            ),
            "coinbase" => (
                Box::new(EvmCoinBase::new_unchecked(inst_set, args[0])),
                true,
            ),
            "timestamp" => (Box::new(EvmTimestamp::new_unchecked(inst_set)), true),
            "number" => (Box::new(EvmNumber::new_unchecked(inst_set)), true),
            "difficulty" => panic!("`difficulty` is no longer supported"),
            "prevrandao" => (Box::new(EvmPrevRandao::new_unchecked(inst_set)), true),
            "gaslimit" => (Box::new(EvmGasLimit::new_unchecked(inst_set)), true),
            "datacopy" => (
                Box::new(EvmCodeCopy::new_unchecked(
                    inst_set, args[0], args[1], args[2],
                )),
                false,
            ),

            f => {
                let callee = self.ctx.lookup_func(f).unwrap();
                let ret_ty = self.builder.module_builder.sig(callee, |sig| sig.ret_ty());
                (
                    Box::new(Call::new_unchecked(inst_set, callee, args.into())),
                    !ret_ty.is_unit(),
                )
            }
        };

        if has_ret {
            Some(self.builder.insert_inst_dyn(inst, Type::I256))
        } else {
            self.builder.insert_inst_no_result_dyn(inst);
            None
        }
    }

    fn ptoi(&mut self, ptr: ValueId) -> ValueId {
        let ptoi = PtrToInt::new_unchecked(self.builder.ctx().inst_set, ptr, Type::I256);
        self.builder.insert_inst(ptoi, Type::I256)
    }

    fn itop(&mut self, ptr: ValueId) -> ValueId {
        let m_ctx = self.builder.ctx();
        let ptr_ty = Type::I256.to_ptr(m_ctx);
        let ptoi = IntToPtr::new_unchecked(m_ctx.inst_set, ptr, ptr_ty);
        self.builder.insert_inst(ptoi, ptr_ty)
    }
}

struct FuncCtx {
    variables: Vec<HashMap<String, Variable>>,
    // (ContinueDest, BreakDest)
    loop_stack: Vec<(BlockId, BlockId)>,
}

impl FuncCtx {
    fn new() -> Self {
        Self {
            variables: vec![HashMap::default()],
            loop_stack: Vec::new(),
        }
    }

    fn declare_var(&mut self, builder: &mut FunctionBuilder<InstInserter>, name: &str) -> Variable {
        let var = builder.declare_var(Type::I256);
        self.variables
            .last_mut()
            .unwrap()
            .insert(name.to_string(), var);
        var
    }

    fn def_var(
        &mut self,
        builder: &mut FunctionBuilder<InstInserter>,
        yul_vars: &[Identifier],
        value: ValueId,
    ) {
        let inst_set = builder.inst_set();

        if yul_vars.len() == 1 {
            let var = self.lookup_var(&yul_vars[0].name);
            builder.def_var(var, value);
        } else {
            for (i, yul_var) in yul_vars.iter().enumerate() {
                let idx = builder.make_imm_value(I256::from_usize(i));
                let extract = ExtractValue::new_unchecked(inst_set, value, idx);
                let elem_value = builder.insert_inst(extract, Type::I256);
                let var = self.lookup_var(&yul_var.name);
                builder.def_var(var, elem_value);
            }
        }
    }

    fn lookup_var(&self, name: &str) -> Variable {
        for vars in self.variables.iter().rev() {
            if let Some(var) = vars.get(name) {
                return *var;
            }
        }

        panic!("variable `{name}` is undefined");
    }
}
