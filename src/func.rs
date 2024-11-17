use std::collections::HashMap;

use sonatina_ir::{
    builder::{FunctionBuilder, ModuleBuilder},
    func_cursor::InstInserter,
    inst::{arith::*, cmp::*, data::*, evm::*, logic::*},
    Inst, Type, ValueId,
};
use yultsur::yul::{Expression, FunctionCall, FunctionDefinition};

use crate::{Ctx, Literal};

pub struct FuncTranspiler<'ctx> {
    ctx: &'ctx mut Ctx,
    builder: FunctionBuilder<InstInserter>,
    yul_func: FunctionDefinition,
    variables: HashMap<String, ValueId>,
}

impl<'ctx> FuncTranspiler<'ctx> {
    pub fn build(mut self) -> ModuleBuilder {
        todo!()
    }

    pub fn expr(&mut self, yul_expr: &Expression) -> Option<ValueId> {
        match yul_expr {
            Expression::Literal(lit) => {
                let lit = Literal::parse(&lit).as_i256().unwrap();
                Some(self.builder.make_imm_value(lit))
            }
            Expression::Identifier(ident) => Some(self.variables[&ident.name]),
            Expression::FunctionCall(call) => self.func_call(call),
        }
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
            "signextend" => todo!(),
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
            "difficulty" => panic!("difficulty is no longer supported"),
            "prevrandao" => (Box::new(EvmPrevRandao::new_unchecked(isb)), true),
            "gaslimit" => (Box::new(EvmGasLimit::new_unchecked(isb)), true),

            _ => {
                todo!()
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
