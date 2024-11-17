use std::collections::HashMap;

use sonatina_ir::{
    builder::{FunctionBuilder, ModuleBuilder},
    func_cursor::InstInserter,
    inst::{arith::*, cmp::*, control_flow::*, data::*, evm::*, logic::*},
    BlockId, Inst, Type, ValueId, Variable,
};
use yultsur::yul::{
    Block as YulBlock, Expression, FunctionCall, FunctionDefinition, Identifier,
    Literal as YulLiteral, Statement,
};

use crate::{Ctx, Literal};

pub struct FuncTranspiler<'ctx> {
    ctx: &'ctx mut Ctx,
    builder: FunctionBuilder<InstInserter>,
    yul_func: FunctionDefinition,
    ret_var: Option<Variable>,
    variables: HashMap<String, Variable>,
    // (ContinueDest, BreakDest)
    loop_stack: Vec<(BlockId, BlockId)>,
}

impl<'ctx> FuncTranspiler<'ctx> {
    pub fn build(mut self) -> ModuleBuilder {
        // TODO: Declare return variables.
        todo!()
    }

    /// Returns `true` if the statement is the terminator.
    pub fn stmt(&mut self, yul_stmt: &Statement) {
        let isb = self.builder.ctx().inst_set;

        match yul_stmt {
            Statement::Block(block) => self.block(block, None),

            Statement::FunctionDefinition(func_def) => {
                todo!()
            }

            Statement::VariableDeclaration(yul_decl) => {
                let yul_vars = &yul_decl.variables;
                for yul_var in yul_vars {
                    let var = self.builder.declare_var(Type::I256);
                    self.variables.insert(yul_var.name.clone(), var);
                }

                let Some(expr) = &yul_decl.value else {
                    return;
                };
                self.assign(yul_vars, expr);
            }

            Statement::Assignment(assign) => self.assign(&assign.variables, &assign.value),

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
                let br = Br::new_unchecked(isb, cond, then_bb, merge_bb);
                self.builder.insert_inst_no_result(br);

                // Enter then block.
                self.builder.switch_to_block(then_bb);
                self.block(&if_.body, Some(then_bb));
                self.builder.switch_to_block(merge_bb);
            }

            Statement::Switch(switch) => {
                let scrutinee = self.expr(&switch.expression).unwrap();
                let current_bb = self.builder.current_block().unwrap();

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
                let merge_bb = self.builder.append_block();

                let mut table = Vec::with_capacity(labeled.len());
                for (value, bb, yul_block) in labeled {
                    self.builder.switch_to_block(bb);
                    self.block(yul_block, Some(merge_bb));
                    table.push((value, bb));
                }

                let br_inst = if let Some((bb, yul_block)) = default {
                    self.builder.switch_to_block(bb);
                    self.block(yul_block, Some(merge_bb));
                    BrTable::new_unchecked(isb, scrutinee, Some(bb), table)
                } else {
                    BrTable::new_unchecked(isb, scrutinee, None, table)
                };

                self.builder.switch_to_block(current_bb);
                self.builder.insert_inst_no_result(br_inst);

                self.builder.switch_to_block(merge_bb);
            }

            Statement::ForLoop(for_) => {
                let lp_header = self.builder.append_block();
                let lp_body = self.builder.append_block();
                let lp_post = self.builder.append_block();
                let lp_exit = self.builder.make_block();
                // todo!(). Scoping rule is weird.
                self.block(&for_.pre, Some(lp_header));

                self.builder.switch_to_block(lp_header);
                let cond = self.expr(&for_.condition).unwrap();
                let br = Br::new_unchecked(isb, cond, lp_body, lp_exit);
                self.builder.insert_inst_no_result(br);

                self.loop_stack.push((lp_post, lp_exit));
                self.builder.switch_to_block(lp_body);
                self.block(&for_.body, Some(lp_post));
                self.loop_stack.pop();

                self.builder.switch_to_block(lp_post);
                self.block(&for_.post, Some(lp_header));

                self.builder.switch_to_block(lp_exit);
            }

            Statement::Break => {
                let break_dest = self.loop_stack.last().unwrap().1;
                let jump = Jump::new_unchecked(isb, break_dest);
                self.builder.insert_inst_no_result(jump);
                self.builder.seal_block();
            }

            Statement::Continue => {
                let break_dest = self.loop_stack.last().unwrap().0;
                let jump = Jump::new_unchecked(isb, break_dest);
                self.builder.insert_inst_no_result(jump);
                self.builder.seal_block();
            }

            Statement::Leave => self.insert_return(),
        }
    }

    fn block(&mut self, yul_block: &YulBlock, fallback_to: Option<BlockId>) {
        self.ctx.enter_block(yul_block);

        let current_bb = self.builder.current_block().unwrap();
        for yul_stmt in &yul_block.statements {
            self.stmt(yul_stmt);
            if self.builder.is_sealed(current_bb) {
                self.ctx.leave_block();
                return;
            }
        }

        if !self.builder.is_sealed(current_bb) {
            self.builder.switch_to_block(current_bb);
            match fallback_to {
                Some(bb) => {
                    let isb = self.builder.ctx().inst_set;
                    let jump = Jump::new_unchecked(isb, bb);
                    self.builder.insert_inst_no_result(jump);
                    self.builder.seal_block();
                }
                None => {
                    self.insert_return();
                }
            }
        }

        self.ctx.leave_block();
    }

    fn insert_return(&mut self) {
        let isb = self.builder.ctx().inst_set;

        let ret_inst = if let Some(ret_var) = self.ret_var {
            let arg = self.builder.use_var(ret_var);
            Return::new_unchecked(isb, Some(arg))
        } else {
            Return::new_unchecked(isb, None)
        };

        self.builder.insert_inst_no_result(ret_inst);
        self.builder.seal_block();
    }

    pub fn assign(&mut self, yul_vars: &[Identifier], expr: &Expression) {
        let value = self.expr(expr).unwrap();

        if yul_vars.len() == 1 {
            let var = self.variables[&yul_vars[0].name];
            self.builder.def_var(var, value);
        } else {
            // Use gep and mload, then def_var for each variables.
            todo!()
        }
    }

    pub fn expr(&mut self, yul_expr: &Expression) -> Option<ValueId> {
        match yul_expr {
            Expression::Literal(lit) => Some(self.lit(lit)),
            Expression::Identifier(ident) => {
                let var = self.variables[&ident.name];
                Some(self.builder.use_var(var))
            }
            Expression::FunctionCall(call) => self.func_call(call),
        }
    }

    fn lit(&mut self, yul_lit: &YulLiteral) -> ValueId {
        let lit = Literal::parse(yul_lit).as_i256().unwrap();
        self.builder.make_imm_value(lit)
    }

    pub fn func_call(&mut self, yul_func_call: &FunctionCall) -> Option<ValueId> {
        let args: Vec<_> = yul_func_call
            .arguments
            .iter()
            .map(|expr| self.expr(expr).unwrap())
            .collect();

        let isb = self.builder.ctx().inst_set;

        let (inst, has_ret): (Box<dyn Inst>, _) = match yul_func_call.function.name.as_str() {
            "stop" => (Box::new(EvmStop::new_unchecked(isb)), false),

            "add" => (Box::new(Add::new_unchecked(isb, args[0], args[1])), true),
            "sub" => (Box::new(Sub::new_unchecked(isb, args[0], args[1])), true),
            "mul" => (Box::new(Mul::new_unchecked(isb, args[0], args[1])), true),
            "div" => (
                Box::new(EvmUdiv::new_unchecked(isb, args[0], args[1])),
                true,
            ),
            "sdiv" => (
                Box::new(EvmSdiv::new_unchecked(isb, args[0], args[1])),
                true,
            ),
            "mod" => (
                Box::new(EvmUmod::new_unchecked(isb, args[0], args[1])),
                true,
            ),
            "smod" => (
                Box::new(EvmSmod::new_unchecked(isb, args[0], args[1])),
                true,
            ),
            "exp" => (Box::new(EvmExp::new_unchecked(isb, args[0], args[1])), true),
            "not" => (Box::new(Not::new_unchecked(isb, args[0])), true),
            "lt" => (Box::new(Lt::new_unchecked(isb, args[0], args[1])), true),
            "gt" => (Box::new(Gt::new_unchecked(isb, args[0], args[1])), true),
            "slt" => (Box::new(Slt::new_unchecked(isb, args[0], args[1])), true),
            "sgt" => (Box::new(Sgt::new_unchecked(isb, args[0], args[1])), true),
            "eq" => (Box::new(Eq::new_unchecked(isb, args[0], args[1])), true),
            "iszero" => (Box::new(IsZero::new_unchecked(isb, args[0])), true),
            "and" => (Box::new(And::new_unchecked(isb, args[0], args[1])), true),
            "or" => (Box::new(Or::new_unchecked(isb, args[0], args[1])), true),
            "byte" => (
                Box::new(EvmByte::new_unchecked(isb, args[0], args[1])),
                true,
            ),
            "shl" => (Box::new(Shl::new_unchecked(isb, args[0], args[1])), true),
            "shr" => (Box::new(Shr::new_unchecked(isb, args[0], args[1])), true),
            "sar" => (Box::new(Sar::new_unchecked(isb, args[0], args[1])), true),
            "addmod" => (
                Box::new(EvmAddMod::new_unchecked(isb, args[0], args[1], args[2])),
                true,
            ),
            "mulmod" => (
                Box::new(EvmMulMod::new_unchecked(isb, args[0], args[1], args[2])),
                true,
            ),
            "signextend" => todo!("Add EvmSignExtend?"),
            "keccak256" => (
                Box::new(EvmKeccak256::new_unchecked(isb, args[0], args[1])),
                true,
            ),
            "pop" => return None,
            "mload" => (
                Box::new(Mload::new_unchecked(isb, args[0], Type::I256)),
                true,
            ),
            "mstore" => (
                Box::new(Mstore::new_unchecked(isb, args[0], args[1], Type::I256)),
                false,
            ),
            "mstore8" => (
                Box::new(EvmMstore8::new_unchecked(isb, args[0], args[1])),
                false,
            ),
            "sload" => (Box::new(EvmSload::new_unchecked(isb, args[0])), true),
            "sstore" => (
                Box::new(EvmSstore::new_unchecked(isb, args[0], args[1])),
                false,
            ),
            "msize" => (Box::new(EvmMsize::new_unchecked(isb)), true),
            "gas" => (Box::new(EvmGas::new_unchecked(isb)), true),
            "address" => (Box::new(EvmGas::new_unchecked(isb)), true),
            "balance" => (Box::new(EvmBalance::new_unchecked(isb, args[0])), true),
            "selfbalance" => (Box::new(EvmSelfBalance::new_unchecked(isb)), true),
            "caller" => (Box::new(EvmCaller::new_unchecked(isb)), true),
            "callvalue" => (Box::new(EvmCallValue::new_unchecked(isb)), true),
            "calldataload" => (Box::new(EvmCallDataLoad::new_unchecked(isb, args[0])), true),
            "calldatasize" => (Box::new(EvmCallDataSize::new_unchecked(isb)), true),
            "calldatacopy" => (
                Box::new(EvmCallDataCopy::new_unchecked(
                    isb, args[0], args[1], args[2],
                )),
                false,
            ),
            "codesize" => (Box::new(EvmCodeSize::new_unchecked(isb)), true),
            "codecopy" => (
                Box::new(EvmCodeCopy::new_unchecked(isb, args[0], args[1], args[2])),
                false,
            ),
            "extcodesize" => (Box::new(EvmExtCodeSize::new_unchecked(isb, args[0])), true),
            "extcodecopy" => (
                Box::new(EvmExtCodeCopy::new_unchecked(
                    isb, args[0], args[1], args[2], args[3],
                )),
                false,
            ),
            "returndatasize" => (Box::new(EvmReturnDataSize::new_unchecked(isb)), true),
            "returndatacopy" => (
                Box::new(EvmReturnDataCopy::new_unchecked(
                    isb, args[0], args[1], args[2],
                )),
                false,
            ),
            "mcopy" => (
                Box::new(EvmMcopy::new_unchecked(isb, args[0], args[1], args[2])),
                false,
            ),
            "extcodehash" => (Box::new(EvmExtCodeHash::new_unchecked(isb, args[0])), true),
            "create" => (
                Box::new(EvmCreate::new_unchecked(isb, args[0], args[1], args[2])),
                true,
            ),
            "create2" => (
                Box::new(EvmCreate2::new_unchecked(
                    isb, args[0], args[1], args[2], args[3],
                )),
                true,
            ),
            "call" => (
                Box::new(EvmCall::new_unchecked(
                    isb, args[0], args[1], args[2], args[3], args[4], args[5], args[6],
                )),
                true,
            ),
            "callcode" => (
                Box::new(EvmCallCode::new_unchecked(
                    isb, args[0], args[1], args[2], args[3], args[4], args[5], args[6],
                )),
                true,
            ),
            "delegatecall" => (
                Box::new(EvmDelegateCall::new_unchecked(
                    isb, args[0], args[1], args[2], args[3], args[4], args[5],
                )),
                true,
            ),
            "staticcall" => (
                Box::new(EvmStaticCall::new_unchecked(
                    isb, args[0], args[1], args[2], args[3], args[4], args[5],
                )),
                true,
            ),
            "return" => (
                Box::new(EvmReturn::new_unchecked(isb, args[0], args[1])),
                false,
            ),
            "revert" => (
                Box::new(EvmRevert::new_unchecked(isb, args[0], args[1])),
                false,
            ),
            "selfdestruct" => (
                Box::new(EvmSelfDestruct::new_unchecked(isb, args[0])),
                false,
            ),
            "invalid" => (Box::new(EvmInvalid::new_unchecked(isb)), false),
            "log0" => (
                Box::new(EvmLog0::new_unchecked(isb, args[0], args[1])),
                false,
            ),
            "log1" => (
                Box::new(EvmLog1::new_unchecked(isb, args[0], args[1], args[2])),
                false,
            ),
            "log2" => (
                Box::new(EvmLog2::new_unchecked(
                    isb, args[0], args[1], args[2], args[3],
                )),
                false,
            ),
            "log3" => (
                Box::new(EvmLog3::new_unchecked(
                    isb, args[0], args[1], args[2], args[3], args[4],
                )),
                false,
            ),
            "log4" => (
                Box::new(EvmLog4::new_unchecked(
                    isb, args[0], args[1], args[2], args[3], args[4], args[5],
                )),
                false,
            ),
            "chainid" => (Box::new(EvmChainId::new_unchecked(isb)), true),
            "basefee" => (Box::new(EvmBaseFee::new_unchecked(isb)), true),
            "blobbasefee" => (Box::new(EvmBlobBaseFee::new_unchecked(isb)), true),
            "origin" => (Box::new(EvmOrigin::new_unchecked(isb)), true),
            "gasprice" => (Box::new(EvmGasPrice::new_unchecked(isb)), true),
            "blobhash" => (Box::new(EvmBlockHash::new_unchecked(isb, args[0])), true),
            "coinbase" => (Box::new(EvmCoinBase::new_unchecked(isb, args[0])), true),
            "timestamp" => (Box::new(EvmTimestamp::new_unchecked(isb)), true),
            "number" => (Box::new(EvmNumber::new_unchecked(isb)), true),
            "difficulty" => panic!("`difficulty` is no longer supported"),
            "prevrandao" => (Box::new(EvmPrevRandao::new_unchecked(isb)), true),
            "gaslimit" => (Box::new(EvmGasLimit::new_unchecked(isb)), true),

            f => {
                let callee = self.ctx.lookup_func(f).unwrap();
                let sig = self.builder.module_builder.sig(callee);
                (
                    Box::new(Call::new_unchecked(isb, callee, args.into())),
                    !sig.ret_ty().is_unit(),
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
}
