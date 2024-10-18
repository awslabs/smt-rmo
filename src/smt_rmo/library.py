# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from functools import reduce
from typing import Any, Callable, Dict

import pysmt.operators as op
from pysmt.environment import Environment, get_env
from pysmt.fnode import FNode
from pysmt.walkers import IdentityDagWalker

from smt_rmo.ddmin import DDMinRewriter
from smt_rmo.rewriters import AnyRewriter, LambdaRewriter

######## DDMin rewriters ########


def AndDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.AND,
        environment.formula_manager.And,
        name="DDMinAnd",
    )


def OrDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.OR,
        environment.formula_manager.Or,
        name="DDMinOr",
    )


def BVAndDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.BV_AND,
        environment.formula_manager.BVAnd,
        name="DDMinBVAnd",
    )


def BVOrDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.BV_OR,
        environment.formula_manager.BVOr,
        name="DDMinBVOr",
    )


def BVConcatDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.BV_CONCAT,
        environment.formula_manager.BVConcat,
        name="DDMinBVConcat",
    )


def BVAddDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.BV_ADD,
        environment.formula_manager.BVAdd,
        name="DDMinBVAdd",
    )


def BVMulDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.BV_MUL,
        environment.formula_manager.BVMul,
        name="DDMinBVMul",
    )


def StrConcatDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.STR_CONCAT,
        environment.formula_manager.StrConcat,
        name="DDMinStrConcat",
    )


def PlusDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.PLUS,
        environment.formula_manager.Plus,
        name="DDMinPlus",
    )


def TimesDDMinRewriter(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
) -> DDMinRewriter:
    return DDMinRewriter(
        assertion_to_formula,
        target_command,
        oracle,
        lambda expr: expr.node_type() == op.TIMES,
        environment.formula_manager.Times,
        name="DDMinTimes",
    )


def DefaultDDMinRewriters(
    assertion_to_formula: Dict[Any, FNode],
    target_command: Any,
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
):
    return [
        AndDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        OrDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        BVAndDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        BVOrDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        # BVConcatDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        BVAddDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        BVMulDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        StrConcatDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        PlusDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
        TimesDDMinRewriter(assertion_to_formula, target_command, oracle, environment),
    ]


######## Greedy rewriters ##########


def replace_bool_expr_with_true(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.TRUE())
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.BOOL())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_bool_expr_with_false(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.FALSE())
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.BOOL())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_int_expr_with_0(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.Int(0))
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.INT())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_int_expr_with_1(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.Int(1))
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.INT())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_real_expr_with_0(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.Real(0))
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.REAL())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_real_expr_with_1(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.Real(1))
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.REAL())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_string_expr_with_empty(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.String(""))
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.STRING())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_regex_expr_with_reall(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.ReAll())
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.REGEX())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_regex_expr_with_reallchars(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.ReAllChar())
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.REGEX())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_bv_expr_with_0(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.BV(
                0,
                width=expr.bv_width(),
                underscore=expr.bv_underscore() if expr.is_bv_constant() else False,
            )
        )
        .guarded(lambda expr, args, env: expr.get_type().is_bv_type())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_bv_expr_with_1(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.BV(
                1,
                width=expr.bv_width(),
                underscore=expr.bv_underscore() if expr.is_bv_constant() else False,
            )
        )
        .guarded(lambda expr, args, env: expr.get_type().is_bv_type())
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_bv_concat_with_zext(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.BVZExt(
                [a for a in args if a.is_bv_constant()][0],
                expr.bv_width() - [a for a in args if a.is_bv_constant()][0].bv_width(),
            )
        )
        .guarded(
            lambda expr, args, env: expr.is_bv_concat()
            and any(c.is_bv_constant() for c in expr.args())
        )
        .checked(oracle_fun)
        .mask_exception()
    )


def replace_by_child(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: [c for c in expr.args() if c.get_type() == expr.get_type()][0]
        )
        .guarded(lambda expr, args, env: any(c.get_type() == expr.get_type() for c in expr.args()))
        .checked(oracle_fun)
        .mask_exception()
    )


def bvite_to_bvcomp(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.BVComp(args[0].arg(0), args[0].arg(1))
        )
        .guarded(
            lambda expr, args, env: expr.is_ite()
            and args[0].is_equals()
            and len(args[0].args()) == 2
            and args[0].arg(0).get_type().is_bv_type()
            and args[1].is_bv_constant()
            and args[2].is_bv_constant()
            and args[1].constant_value() == 1
            and args[1].bv_width() == 1
            and args[2].constant_value() == 0
            and args[2].bv_width() == 1
        )
        .checked(oracle_fun)
        .mask_exception()
    )


def relax_le(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.Equals(args[0], args[1]))
        .guarded(lambda expr, args, env: expr.is_le())
        .checked(oracle_fun)
        .mask_exception()
    )


def relax_ge(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: env.formula_manager.Equals(args[0], args[1]))
        .guarded(lambda expr, args, env: expr.is_ge())
        .checked(oracle_fun)
        .mask_exception()
    )


# new_fresh_symbol
def replace_real_expr_with_fresh(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.new_fresh_symbol(
                env.type_manager.REAL(), "FreshReal%d"
            )
        )
        .guarded(lambda expr, args, env: expr.get_type() == env.type_manager.REAL())
        .checked(oracle_fun)
    )


def replace_extract_bv_constant(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.BV(
                "#b%s"
                % args[0].bv_bin_str(reverse=True)[
                    expr.bv_extract_start() : expr.bv_extract_end() + 1
                ][::-1],
                width=expr.bv_extract_end() - expr.bv_extract_start() + 1,
            )
        )
        .guarded(lambda expr, args, env: expr.is_bv_extract() and expr.arg(0).is_bv_constant())
        .checked(oracle_fun)
    )


def DEFAULT_GREEDY_REWRITERS(oracle_fun):
    return AnyRewriter(
        replace_bool_expr_with_true(oracle_fun),
        replace_bool_expr_with_false(oracle_fun),
        replace_int_expr_with_0(oracle_fun),
        replace_int_expr_with_1(oracle_fun),
        replace_real_expr_with_0(oracle_fun),
        replace_real_expr_with_1(oracle_fun),
        replace_bv_expr_with_0(oracle_fun),
        replace_bv_expr_with_1(oracle_fun),
        replace_by_child(oracle_fun),
        replace_bv_concat_with_zext(oracle_fun),
        bvite_to_bvcomp(oracle_fun),
        replace_real_expr_with_fresh(oracle_fun),
        replace_extract_bv_constant(oracle_fun),
    )


############### simplifiers / normalizers ###################


def replace_double_negation(oracle_fun):
    return (
        LambdaRewriter(lambda expr, args, env: expr.arg(0))
        .guarded(lambda expr, args, env: expr.is_not() and expr.arg(0).is_not())
        .checked(oracle_fun)
    )


def flatten_nested_and(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.And(
                reduce(
                    lambda a, b: a + b,
                    [list(c.args()) if c.is_and() else [c] for c in expr.args()],
                )
            )
        )
        .guarded(lambda expr, args, env: expr.is_and() and any(c.is_and() for c in expr.args()))
        .checked(oracle_fun)
    )


def flatten_nested_or(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.Or(
                reduce(
                    lambda a, b: a + b,
                    [list(c.args()) if c.is_and() else [c] for c in expr.args()],
                )
            )
        )
        .guarded(lambda expr, args, env: expr.is_or() and any(c.is_or() for c in expr.args()))
        .checked(oracle_fun)
    )


def rewrite_implies(oracle_fun):
    return (
        LambdaRewriter(
            lambda expr, args, env: env.formula_manager.Or(
                env.formula_manager.Not(expr.arg(0)), expr.arg(1)
            )
        )
        .guarded(lambda expr, args, env: expr.is_implies())
        .checked(oracle_fun)
    )


def DEFAULT_NORMALIZERS(oracle_fun):
    return AnyRewriter(
        replace_double_negation(oracle_fun),
        flatten_nested_and(oracle_fun),
        flatten_nested_or(oracle_fun),
        rewrite_implies(oracle_fun),
    )


################## utility rewriters ##################


class LetExpansionWalker(IdentityDagWalker):
    def __init__(self, target_expr: FNode = None, env=None, invalidate_memoization=None):
        super().__init__(env, invalidate_memoization)
        self._target: FNode = target_expr

    def walk_let(self, formula, args, **kwargs):
        if self._target is None or formula == self._target:
            defs = {self.memoization[v]: self.memoization[e] for v, e in formula.let_defs()}
            return self.env.substituter.substitute(args[0], defs, None)
        else:
            return super().walk_let(formula, args, **kwargs)
