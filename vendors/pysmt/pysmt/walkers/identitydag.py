#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
from pysmt.fnode import FNode
from pysmt.utils import ImmutableAnnotations
from pysmt.walkers.dag import DagWalker


class IdentityDagWalker(DagWalker):
    """This class traverses a formula and rebuilds it recursively
    identically.

    This could be useful when only some nodes needs to be rewritten
    but the structure of the formula has to be kept.

    """

    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self, env=env, invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager

    def walk_symbol(self, formula, args, **kwargs):
        return self.mgr.Symbol(formula.symbol_name(), formula.symbol_type())

    def walk_algebraic_constant(self, formula, args, **kwargs):
        return self.mgr._Algebraic(formula.constant_value())

    def walk_real_constant(self, formula, args, **kwargs):
        return self.mgr.Real(formula.constant_value())

    def walk_int_constant(self, formula, args, **kwargs):
        return self.mgr.Int(formula.constant_value())

    def walk_bool_constant(self, formula, args, **kwargs):
        return self.mgr.Bool(formula.constant_value())

    def walk_str_constant(self, formula, **kwargs):
        return self.mgr.String(formula.constant_value())

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(args)

    def walk_or(self, formula, args, **kwargs):
        return self.mgr.Or(args)

    def walk_not(self, formula, args, **kwargs):
        return self.mgr.Not(args[0])

    def walk_iff(self, formula, args, **kwargs):
        return self.mgr.Iff(args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return self.mgr.Implies(args[0], args[1])

    def walk_equals(self, formula, args, **kwargs):
        return self.mgr.Equals(args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        return self.mgr.Ite(args[0], args[1], args[2])

    def walk_le(self, formula, args, **kwargs):
        return self.mgr.LE(args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.mgr.LT(args[0], args[1])

    def walk_forall(self, formula, args, **kwargs):
        qvars = [self.walk_symbol(v, args, **kwargs) for v in formula.quantifier_vars()]
        return self.mgr.ForAll(qvars, args[0])

    def walk_exists(self, formula, args, **kwargs):
        qvars = [self.walk_symbol(v, args, **kwargs) for v in formula.quantifier_vars()]
        return self.mgr.Exists(qvars, args[0])

    def walk_let(self, formula, args, **kwargs):
        defs = [
            (self.memoization[v], self.memoization[e]) for v, e in formula.let_defs()
        ]
        defs = tuple(zip(*defs))
        return self.mgr.Let(defs[0], defs[1], args[0])

    def walk_plus(self, formula, args, **kwargs):
        return self.mgr.Plus(args)

    def walk_times(self, formula, args, **kwargs):
        return self.mgr.Times(args)

    def walk_pow(self, formula, args, **kwargs):
        return self.mgr.Pow(args[0], args[1])

    def walk_minus(self, formula, args, **kwargs):
        return self.mgr.Minus(args[0], args[1])

    def walk_function(self, formula, args, **kwargs):
        # We re-create the symbol name
        old_name = formula.function_name()
        new_name = self.walk_symbol(old_name, args, **kwargs)
        return self.mgr.Function(new_name, args)

    def walk_toreal(self, formula, args, **kwargs):
        return self.mgr.ToReal(args[0])

    def walk_real_to_int(self, formula, args, **kwargs):
        return self.mgr.RealToInt(args[0])

    def walk_bv_constant(self, formula, **kwargs):
        return self.mgr.BV(
            formula.constant_value(),
            formula.bv_width(),
            underscore=formula.bv_underscore(),
            hexadecimal=formula.bv_hex(),
        )

    def walk_bv_and(self, formula, args, **kwargs):
        return self.mgr.BVAnd(*args)

    def walk_bv_nand(self, formula, args, **kwargs):
        return self.mgr.BVNand(args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        return self.mgr.BVNot(args[0])

    def walk_bv_neg(self, formula, args, **kwargs):
        return self.mgr.BVNeg(args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        return self.mgr.BVOr(*args)

    def walk_bv_nor(self, formula, args, **kwargs):
        return self.mgr.BVNor(args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        return self.mgr.BVXor(args[0], args[1])

    def walk_bv_xnor(self, formula, args, **kwargs):
        return self.mgr.BVXnor(args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        return self.mgr.BVAdd(*args)

    def walk_bv_sub(self, formula, args, **kwargs):
        return self.mgr.BVSub(args[0], args[1])

    def walk_bv_mul(self, formula, args, **kwargs):
        return self.mgr.BVMul(*args)

    def walk_bv_udiv(self, formula, args, **kwargs):
        return self.mgr.BVUDiv(args[0], args[1])

    def walk_bv_urem(self, formula, args, **kwargs):
        return self.mgr.BVURem(args[0], args[1])

    def walk_bv_ult(self, formula, args, **kwargs):
        return self.mgr.BVULT(args[0], args[1])

    def walk_bv_ugt(self, formula, args, **kwargs):
        return self.mgr.BVUGT(args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self.mgr.BVULE(args[0], args[1])
    
    def walk_bv_uge(self, formula, args, **kwargs):
        return self.mgr.BVUGE(args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        return self.mgr.BVExtract(
            args[0], start=formula.bv_extract_start(), end=formula.bv_extract_end()
        )

    def walk_bv_ror(self, formula, args, **kwargs):
        return self.mgr.BVRor(args[0], formula.bv_rotation_step())

    def walk_bv_rol(self, formula, args, **kwargs):
        return self.mgr.BVRol(args[0], formula.bv_rotation_step())

    def walk_bv_sext(self, formula, args, **kwargs):
        return self.mgr.BVSExt(args[0], formula.bv_extend_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        return self.mgr.BVZExt(args[0], formula.bv_extend_step())

    def walk_bv_concat(self, formula, args, **kwargs):
        return self.mgr.BVConcat(args)

    def walk_bv_lshl(self, formula, args, **kwargs):
        return self.mgr.BVLShl(args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        return self.mgr.BVLShr(args[0], args[1])

    def walk_bv_ashr(self, formula, args, **kwargs):
        return self.mgr.BVAShr(args[0], args[1])

    def walk_bv_comp(self, formula, args, **kwargs):
        return self.mgr.BVComp(args[0], args[1])

    def walk_bv_slt(self, formula, args, **kwargs):
        return self.mgr.BVSLT(args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        return self.mgr.BVSLE(args[0], args[1])

    def walk_bv_sdiv(self, formula, args, **kwargs):
        return self.mgr.BVSDiv(args[0], args[1])

    def walk_bv_srem(self, formula, args, **kwargs):
        return self.mgr.BVSRem(args[0], args[1])

    def walk_bv_smod(self, formula, args, **kwargs):
        return self.mgr.BVSMod(args[0], args[1])

    def walk_str_length(self, formula, args, **kwargs):
        return self.mgr.StrLength(args[0])

    def walk_str_concat(self, formula, args, **kwargs):
        return self.mgr.StrConcat(args)

    def walk_str_contains(self, formula, args, **kwargs):
        return self.mgr.StrContains(args[0], args[1])

    def walk_str_indexof(self, formula, args, **kwargs):
        return self.mgr.StrIndexOf(args[0], args[1], args[2])

    def walk_str_replace(self, formula, args, **kwargs):
        return self.mgr.StrReplace(args[0], args[1], args[2])

    def walk_str_replace_all(self, formula, args, **kwargs):
        return self.mgr.StrReplaceAll(args[0], args[1], args[2])

    def walk_str_compare(self, formula, args, **kwargs):
        return self.mgr.StrCompare(args[0], args[1])

    def walk_str_substr(self, formula, args, **kwargs):
        return self.mgr.StrSubstr(args[0], args[1], args[2])

    def walk_str_prefixof(self, formula, args, **kwargs):
        return self.mgr.StrPrefixOf(args[0], args[1])

    def walk_str_suffixof(self, formula, args, **kwargs):
        return self.mgr.StrSuffixOf(args[0], args[1])

    def walk_str_to_int(self, formula, args, **kwargs):
        return self.mgr.StrToInt(args[0])

    def walk_str_to_re(self, formula, args, **kwargs):
        return self.mgr.StrToRe(args[0])

    def walk_str_in_re(self, formula, args, **kwargs):
        return self.mgr.StrInRe(args[0], args[1])

    def walk_str_replace_re(self, formula, args, **kwargs):
        return self.mgr.StrReplaceRe(args[0], args[1], args[2])

    def walk_str_replace_re_all(self, formula, args, **kwargs):
        return self.mgr.StrReplaceReAll(args[0], args[1], args[2])

    def walk_re_all(self, formula, args, **kwargs):
        return self.mgr.ReAll()

    def walk_re_allchar(self, formula, args, **kwargs):
        return self.mgr.ReAllChar()

    def walk_re_none(self, formula, args, **kwargs):
        return self.mgr.ReNone()

    def walk_re_concat(self, formula, args, **kwargs):
        return self.mgr.ReConcat(args)

    def walk_re_inter(self, formula, args, **kwargs):
        return self.mgr.ReInter(args)

    def walk_re_union(self, formula, args, **kwargs):
        return self.mgr.ReUnion(args)

    def walk_re_star(self, formula, args, **kwargs):
        return self.mgr.ReStar(args[0])

    def walk_re_comp(self, formula, args, **kwargs):
        return self.mgr.ReComp(args[0])

    def walk_re_diff(self, formula, args, **kwargs):
        return self.mgr.ReDiff(args[0], args[1])

    def walk_re_plus(self, formula, args, **kwargs):
        return self.mgr.RePlus(args[0])

    def walk_re_opt(self, formula, args, **kwargs):
        return self.mgr.ReOpt(args[0])

    def walk_re_range(self, formula, args, **kwargs):
        return self.mgr.ReRange(args[0], args[1])

    def walk_re_power(self, formula, args, **kwargs):
        re_exponent = formula.re_power_exponent()
        return self.mgr.RePower(args[0], re_exponent)

    def walk_re_loop(self, formula, args, **kwargs):
        re_loop_bounds = formula.re_loop_bounds()
        return self.mgr.ReLoop(args[0], re_loop_bounds[0], re_loop_bounds[1])

    def walk_int_to_str(self, formula, args, **kwargs):
        return self.mgr.IntToStr(args[0])

    def walk_str_charat(self, formula, args, **kwargs):
        return self.mgr.StrCharAt(args[0], args[1])

    def walk_bv_tonatural(self, formula, args, **kwargs):
        return self.mgr.BVToNatural(args[0])

    def walk_bv_to_int(self, formula, args, **kwargs):
        return self.mgr.BVToNatural(args[0])

    def walk_int_to_bv(self, formula, args, **kwargs):
        return self.mgr.IntToBV(args[0], formula.bv_width())

    def walk_is(self, formula, args, **kwargs):
        old_constructor = formula.constructor()
        new_constructor = self.walk_symbol(old_constructor, args, **kwargs)
        return self.mgr.Is(new_constructor, args[0])

    def walk_array_select(self, formula, args, **kwargs):
        return self.mgr.Select(args[0], args[1])

    def walk_array_store(self, formula, args, **kwargs):
        return self.mgr.Store(args[0], args[1], args[2])

    def walk_array_value(self, formula, args, **kwargs):
        assign = dict(zip(args[1::2], args[2::2]))
        return self.mgr.Array(formula.array_value_index_type(), args[0], assign)

    def walk_div(self, formula, args, **kwargs):
        return self.mgr.Div(args[0], args[1])

    def walk_floor_div(self, formula, args, **kwargs):
        return self.mgr.FloorDiv(args[0], args[1])

    def walk_mod(self, formula, args, **kwargs):
        return self.mgr.Mod(args[0], args[1])

    def walk_abs(self, formula, args, **kwargs):
        return self.mgr.Abs(args[0])

    def walk_ge(self, formula, args, **kwargs):
        return self.mgr.GE(args[0], args[1])

    def walk_gt(self, formula, args, **kwargs):
        return self.mgr.GT(args[0], args[1])

    def walk_annotation(self, formula, args, **kwargs):
        # deep traversal of annotation
        annotations = formula.get_annotations()
        new_annotations = ImmutableAnnotations()
        for k in annotations:
            values = annotations[k]
            for v in values:
                if isinstance(v, tuple):
                    # it is a list of s-expr (FNodes), which should each be traversed
                    new_v = tuple([self.walk(sexpr, **kwargs) for sexpr in v])
                elif isinstance(v, FNode):
                    new_v = self.walk(v, **kwargs)
                else:
                    # a string
                    new_v = v
                new_annotations = new_annotations.add(k, new_v)

        return self.mgr.Annotation(args[0], new_annotations)
