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
from io import StringIO
from pysmt.constants import is_pysmt_fraction
from pysmt.fnode import FNode

import pysmt.operators as op
from pysmt.environment import Environment, get_env
from pysmt.walkers import TreeWalker, DagWalker, handles
from pysmt.utils import quote
from decimal import Decimal, getcontext

class SmtPrinter(TreeWalker):
    def __init__(self, stream, environment:Environment = get_env()):
        TreeWalker.__init__(self)
        self.stream = stream
        self.write = self.stream.write
        self.mgr = environment.formula_manager

    def printer(self, f):
        self.walk(f)

    def walk_threshold(self, formula):
        """This is a complete printer"""
        raise NotImplementedError

    def walk_nary(self, formula, operator):
        self.write("(%s" % operator)
        for s in formula.args():
            self.write(" ")
            yield s
        self.write(")")

    def walk_annotation(self, formula):
        self.write("(! ")
        yield formula.arg(0)
        annotations = formula.get_annotations().as_dict()
        for k in annotations:
            values = annotations[k]
            for v in values:
                if isinstance(v, tuple):
                    self.write(f" :{k} (")
                    for sexpr in v:
                        yield sexpr
                        self.write(" ")
                    self.write(") ")
                elif isinstance(v, FNode):
                    self.write(f" :{k} ")
                    yield v
                else:
                    self.write(f" :{k} {v}")
        self.write(")")

    def walk_and(self, formula):
        return self.walk_nary(formula, "and")

    def walk_or(self, formula):
        return self.walk_nary(formula, "or")

    def walk_not(self, formula):
        return self.walk_nary(formula, "not")

    def walk_implies(self, formula):
        return self.walk_nary(formula, "=>")

    def walk_iff(self, formula):
        return self.walk_nary(formula, "=")

    def walk_plus(self, formula):
        return self.walk_nary(formula, "+")

    def walk_minus(self, formula):
        return self.walk_nary(formula, "-")

    def walk_times(self, formula):
        return self.walk_nary(formula, "*")

    def walk_equals(self, formula):
        return self.walk_nary(formula, "=")

    def walk_le(self, formula):
        return self.walk_nary(formula, "<=")

    def walk_lt(self, formula):
        return self.walk_nary(formula, "<")

    def walk_ge(self, formula):
        return self.walk_nary(formula, ">=")

    def walk_gt(self, formula):
        return self.walk_nary(formula, ">")

    def walk_ite(self, formula):
        return self.walk_nary(formula, "ite")

    def walk_toreal(self, formula):
        return self.walk_nary(formula, "to_real")

    def walk_real_to_int(self, formula):
        return self.walk_nary(formula, "to_int")

    def walk_div(self, formula):
        return self.walk_nary(formula, "/")

    def walk_floor_div(self, formula):
        return self.walk_nary(formula, "div")

    def walk_mod(self, formula):
        return self.walk_nary(formula, "mod")

    def walk_abs(self, formula):
        return self.walk_nary(formula, "abs")

    def walk_pow(self, formula):
        return self.walk_nary(formula, "pow")

    def walk_bv_and(self, formula):
        return self.walk_nary(formula, "bvand")

    def walk_bv_nand(self, formula):
        return self.walk_nary(formula, "bvnand")

    def walk_bv_or(self, formula):
        return self.walk_nary(formula, "bvor")

    def walk_bv_nor(self, formula):
        return self.walk_nary(formula, "bvnor")

    def walk_bv_not(self, formula):
        return self.walk_nary(formula, "bvnot")

    def walk_bv_xor(self, formula):
        return self.walk_nary(formula, "bvxor")

    def walk_bv_xnor(self, formula):
        return self.walk_nary(formula, "bvxnor")

    def walk_bv_add(self, formula):
        return self.walk_nary(formula, "bvadd")

    def walk_bv_sub(self, formula):
        return self.walk_nary(formula, "bvsub")

    def walk_bv_neg(self, formula):
        return self.walk_nary(formula, "bvneg")

    def walk_bv_mul(self, formula):
        return self.walk_nary(formula, "bvmul")

    def walk_bv_udiv(self, formula):
        return self.walk_nary(formula, "bvudiv")

    def walk_bv_urem(self, formula):
        return self.walk_nary(formula, "bvurem")

    def walk_bv_lshl(self, formula):
        return self.walk_nary(formula, "bvshl")

    def walk_bv_lshr(self, formula):
        return self.walk_nary(formula, "bvlshr")

    def walk_bv_ult(self, formula):
        return self.walk_nary(formula, "bvult")

    def walk_bv_ugt(self, formula):
        return self.walk_nary(formula, "bvugt")

    def walk_bv_ule(self, formula):
        return self.walk_nary(formula, "bvule")

    def walk_bv_uge(self, formula):
        return self.walk_nary(formula, "bvuge")

    def walk_bv_slt(self, formula):
        return self.walk_nary(formula, "bvslt")

    def walk_bv_sle(self, formula):
        return self.walk_nary(formula, "bvsle")

    def walk_bv_concat(self, formula):
        return self.walk_nary(formula, "concat")

    def walk_bv_comp(self, formula):
        return self.walk_nary(formula, "bvcomp")

    def walk_bv_ashr(self, formula):
        return self.walk_nary(formula, "bvashr")

    def walk_bv_sdiv(self, formula):
        return self.walk_nary(formula, "bvsdiv")

    def walk_bv_srem(self, formula):
        return self.walk_nary(formula, "bvsrem")

    def walk_bv_smod(self, formula):
        return self.walk_nary(formula, "bvsmod")

    def walk_bv_tonatural(self, formula):
        return self.walk_nary(formula, "bv2nat")

    def walk_bv_to_int(self, formula):
        return self.walk_nary(formula, "bv2int")

    def walk_array_select(self, formula):
        return self.walk_nary(formula, "select")

    def walk_array_store(self, formula):
        return self.walk_nary(formula, "store")

    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name()))

    def walk_function(self, formula):
        return self.walk_nary(formula, quote(formula.function_name().symbol_name()))

    def walk_int_constant(self, formula):
        if formula.constant_value() < 0:
            self.write("(- " + str(-formula.constant_value()) + ")")
        else:
            self.write(str(formula.constant_value()))

    def walk_real_constant(self, formula):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        constant_value = formula.constant_value()

        if is_pysmt_fraction(constant_value):
            (n, d) = (
                abs(formula.constant_value().numerator),
                formula.constant_value().denominator,
            )
            if d != 1:
                # print as decimal
                # set very large precision
                getcontext().prec = 999_999
                d = Decimal(n) / Decimal(d)
                d = d if d >= 0 else -d
                res = template % str(d)
            else:
                n = n if n >= 0 else -n
                res = template % (str(n) + ".0")
        else:
            # use default encoding of the value type
            constant_value = constant_value if constant_value >= 0 else -constant_value
            res = str(constant_value)
            if "." not in res:
                res += ".0"
            res = template % res

        self.write(res)

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("true")
        else:
            self.write("false")

    def walk_bv_constant(self, formula):
        if formula.bv_hex():
            self.write("#x" + formula.bv_str(fmt="x"))
        elif formula.bv_underscore():
            self.write(f"(_ bv{formula.bv_str(fmt='d')} {str(formula.bv_width())} )")
        else:
            self.write("#b" + formula.bv_bin_str())

    def walk_str_constant(self, formula):
        if formula.str_unary_hex():
            c = formula.constant_value()
            self.write(f"(_ char {c})")
        else:
            self.write('"' + formula.constant_value().replace('"', '""') + '"')

    def walk_let(self, formula):
        if len(formula.let_defs()) > 0:
            self.write("(let (")
            for k, v in formula.let_defs():
                self.write("(")
                yield k
                self.write(" ")
                yield v
                self.write(") ")
            self.write(") ")
            yield formula.arg(0)
            self.write(") ")
        else:
            yield formula.arg(0)

    def walk_forall(self, formula):
        return self._walk_quantifier("forall", formula)

    def walk_exists(self, formula):
        return self._walk_quantifier("exists", formula)

    def _walk_quantifier(self, operator, formula):
        assert len(formula.quantifier_vars()) > 0
        self.write("(%s (" % operator)

        for s in formula.quantifier_vars():
            self.write("(")
            yield s
            self.write(" %s)" % s.symbol_type().as_smtlib(False))

        self.write(") ")
        yield formula.arg(0)
        self.write(")")

    def walk_bv_extract(self, formula):
        self.write(
            "((_ extract %d %d) "
            % (formula.bv_extract_end(), formula.bv_extract_start())
        )
        yield formula.arg(0)
        self.write(")")

    @handles(op.BV_ROR, op.BV_ROL)
    def walk_bv_rotate(self, formula):
        if formula.is_bv_ror():
            rotate_type = "rotate_right"
        else:
            assert formula.is_bv_rol()
            rotate_type = "rotate_left"
        self.write("((_ %s %d) " % (rotate_type, formula.bv_rotation_step()))
        yield formula.arg(0)
        self.write(")")

    @handles(op.BV_ZEXT, op.BV_SEXT)
    def walk_bv_extend(self, formula):
        if formula.is_bv_zext():
            extend_type = "zero_extend"
        else:
            assert formula.is_bv_sext()
            extend_type = "sign_extend"
        self.write("((_ %s %d) " % (extend_type, formula.bv_extend_step()))
        yield formula.arg(0)
        self.write(")")

    def walk_str_length(self, formula):
        return self.walk_nary(formula, "str.len")

    def walk_str_charat(self, formula, **kwargs):
        return self.walk_nary(formula, "str.at")

    def walk_str_concat(self, formula, **kwargs):
        return self.walk_nary(formula, "str.++")

    def walk_str_contains(self, formula, **kwargs):
        return self.walk_nary(formula, "str.contains")

    def walk_str_indexof(self, formula, **kwargs):
        return self.walk_nary(formula, "str.indexof")

    def walk_str_replace(self, formula, **kwargs):
        return self.walk_nary(formula, "str.replace")

    def walk_str_replace_all(self, formula, **kwargs):
        return self.walk_nary(formula, "str.replace_all")

    def walk_str_replace_re(self, formula, **kwargs):
        return self.walk_nary(formula, "str.replace_re")

    def walk_str_replace_re_all(self, formula, **kwargs):
        return self.walk_nary(formula, "str.replace_re_all")

    def walk_str_compare(self, formula, **kwargs):
        return self.walk_nary(formula, "str.<=")

    def walk_str_substr(self, formula, **kwargs):
        return self.walk_nary(formula, "str.substr")

    def walk_str_prefixof(self, formula, **kwargs):
        return self.walk_nary(formula, "str.prefixof")

    def walk_str_suffixof(self, formula, **kwargs):
        return self.walk_nary(formula, "str.suffixof")

    def walk_str_to_int(self, formula, **kwargs):
        return self.walk_nary(formula, "str.to_int")
        # self.write("( str.to_int ")
        # yield formula.arg(0)
        # self.write(")")

    def walk_str_to_re(self, formula, **kwargs):
        return self.walk_nary(formula, "str.to_re")
        # self.write("( str.to_re ")
        # yield formula.arg(0)
        # self.write(")")

    def walk_str_in_re(self, formula, **kwargs):
        return self.walk_nary(formula, "str.in_re")

    def walk_re_all(self, formula, **kwargs):
        self.write("re.all")

    def walk_re_allchar(self, formula, **kwargs):
        self.write("re.allchar")

    def walk_re_none(self, formula, **kwargs):
        self.write("re.none")

    def walk_re_concat(self, formula, **kwargs):
        return self.walk_nary(formula, "re.++")

    def walk_re_inter(self, formula, **kwargs):
        return self.walk_nary(formula, "re.inter")

    def walk_re_union(self, formula, **kwargs):
        return self.walk_nary(formula, "re.union")

    def walk_re_star(self, formula, **kwargs):
        return self.walk_nary(formula, "re.*")
        # self.write("( re.* ")
        # yield formula.arg(0)
        # self.write(")")

    def walk_re_comp(self, formula, **kwargs):
        return self.walk_nary(formula, "re.comp")
        # self.write("( re.comp ")
        # yield formula.arg(0)
        # self.write(")")

    def walk_re_diff(self, formula, **kwargs):
        return self.walk_nary(formula, "re.diff")

    def walk_re_plus(self, formula, **kwargs):
        return self.walk_nary(formula, "re.+")
        # self.write("( re.+ ")
        # yield formula.arg(0)
        # self.write(")")

    def walk_re_opt(self, formula, **kwargs):
        return self.walk_nary(formula, "re.opt")
        # self.write("( re.opt ")
        # self.walk(formula.arg(0))
        # self.write(")")

    def walk_re_range(self, formula, **kwargs):
        return self.walk_nary(formula, "re.range")

    def walk_re_power(self, formula, **kwargs):
        assert formula.is_re_power()
        exponent = formula.re_power_exponent()
        self.write(f"( (_ re.^ {exponent}) ")
        yield formula.arg(0)
        self.write(")")

    def walk_re_loop(self, formula, **kwargs):
        assert formula.is_re_loop()
        lb, ub = formula.re_loop_bounds()
        self.write(f"( (_ re.loop {lb} {ub}) ")
        yield formula.arg(0)
        self.write(")")

    def walk_rne(self, formula, **kwargs):
        self.write("RNE")

    def walk_rne(self, formula, **kwargs):
        self.write("RNA")

    def walk_rtp(self, formula, **kwargs):
        self.write("RTP")

    def walk_rtn(self, formula, **kwargs):
        self.write("RTN")

    def walk_rtz(self, formula, **kwargs):
        self.write("RTZ")

    def walk_int_to_str(self, formula, **kwargs):
        return self.walk_nary(formula, "str.from_int")
        # self.write("( str.from_int ")
        # self.walk(formula.arg(0))
        # self.write(")")

    def walk_array_value(self, formula):
        assign = formula.array_value_assigned_values_map()
        for _ in range(len(assign)):
            self.write("(store ")

        self.write("((as const %s) " % formula.get_type().as_smtlib(False))
        yield formula.array_value_default()
        self.write(")")

        for k in sorted(assign, key=str):
            self.write(" ")
            yield k
            self.write(" ")
            yield assign[k]
            self.write(")")

    def walk_is(self, formula):
        self.write("((_ is ")
        yield formula.constructor()
        self.write(") ")
        yield formula.arg(0)
        self.write(")")

    def walk_int_to_bv(self, formula):
        self.write("((_ int2bv ")
        self.write(str(formula.bv_width()))
        self.write(") ")
        yield formula.arg(0)
        self.write(")")


class SmtDagPrinter(DagWalker):
    def __init__(
        self, stream, template=".def_%d", name_seed: int = 0, environment:Environment = get_env()
    ):
        DagWalker.__init__(self, invalidate_memoization=True)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = name_seed
        self.template = template
        self.names = None
        self.mgr = environment.formula_manager

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():  # or formula.is_let():
            # 1. We invoke the relevant function (walk_exists or
            #    walk_forall) to print the formula
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=None, **kwargs)

            # 2. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            DagWalker._push_with_children_to_stack(self, formula, **kwargs)

    def printer(self, f, name_seed: int = 0):
        self.openings = 0
        self.name_seed = name_seed
        self.names = set(quote(x.symbol_name()) for x in f.get_free_variables())

        key = self.walk(f)
        self.write(key)
        self.write(")" * self.openings)

    def _new_symbol(self):
        while (self.template % self.name_seed) in self.names:
            self.name_seed += 1
        res = self.template % self.name_seed
        self.name_seed += 1
        return res

    def walk_let(self, formula, args):
        assert args is not None
        assert len(formula.let_defs()) > 0
        sym = self._new_symbol()
        self.openings += 1

        self.write("(let ((%s (let (" % sym)

        for k, v in formula.let_defs():
            self.write("(")
            self.write(quote(k.symbol_name()))
            self.write(" ")
            self.write(self.memoization[v])
            self.write(") ")

        self.write(") ")
        self.write(args[0])
        self.write("))) ")
        return sym

    def walk_nary(self, formula, args, operator):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, operator))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_annotation(self, formula, args):
            assert args is not None
            sym = self._new_symbol()
            self.openings += 1
            
            
            self.write(f"(let (({sym} ")
            
            self.write("(! ")
            self.write(args[0])
            annotations = formula.get_annotations().as_dict()
            
            subprinter = SmtDagPrinter(self.stream)
            
            for k in annotations:
                values = annotations[k]
                for v in values:
                    if isinstance(v, tuple):
                        self.write(f" :{k} (")
                        for sexpr in v:
                            if isinstance(sexpr, FNode):
                                subprinter.printer(sexpr, name_seed=self.name_seed)
                            else:
                                self.write(f"{sexpr}")
                            self.write(" ")
                        self.write(") ")
                    elif isinstance(v, FNode):
                        self.write(f" :{k} ")
                        subprinter.printer(v, name_seed=self.name_seed)
                    else:
                        self.write(f" :{k} {v}")
            
            self.name_seed = subprinter.name_seed

            self.write(")) ")
            return sym
    
            

    def walk_and(self, formula, args):
        return self.walk_nary(formula, args, "and")

    def walk_or(self, formula, args):
        return self.walk_nary(formula, args, "or")

    def walk_not(self, formula, args):
        return self.walk_nary(formula, args, "not")

    def walk_implies(self, formula, args):
        return self.walk_nary(formula, args, "=>")

    def walk_iff(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_plus(self, formula, args):
        return self.walk_nary(formula, args, "+")

    def walk_minus(self, formula, args):
        return self.walk_nary(formula, args, "-")

    def walk_times(self, formula, args):
        return self.walk_nary(formula, args, "*")

    def walk_equals(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_le(self, formula, args):
        return self.walk_nary(formula, args, "<=")

    def walk_lt(self, formula, args):
        return self.walk_nary(formula, args, "<")

    def walk_ge(self, formula, args):
        return self.walk_nary(formula, args, ">=")

    def walk_gt(self, formula, args):
        return self.walk_nary(formula, args, ">")

    def walk_ite(self, formula, args):
        return self.walk_nary(formula, args, "ite")

    def walk_toreal(self, formula, args):
        return self.walk_nary(formula, args, "to_real")

    def walk_real_to_int(self, formula, args):
        return self.walk_nary(formula, args, "to_int")

    def walk_div(self, formula, args):
        return self.walk_nary(formula, args, "/")

    def walk_floor_div(self, formula, args):
        return self.walk_nary(formula, args, "div")

    def walk_mod(self, formula, args):
        return self.walk_nary(formula, args, "mod")

    def walk_abs(self, formula, args):
        return self.walk_nary(formula, args, "abs")

    def walk_pow(self, formula, args):
        return self.walk_nary(formula, args, "pow")

    def walk_bv_and(self, formula, args):
        return self.walk_nary(formula, args, "bvand")

    def walk_bv_nand(self, formula, args):
        assert len(args) == 2
        return self.walk_nary(formula, args, "bvnand")

    def walk_bv_or(self, formula, args):
        return self.walk_nary(formula, args, "bvor")

    def walk_bv_nor(self, formula, args):
        assert len(args) == 2
        return self.walk_nary(formula, args, "bvnor")

    def walk_bv_not(self, formula, args):
        return self.walk_nary(formula, args, "bvnot")

    def walk_bv_xor(self, formula, args):
        return self.walk_nary(formula, args, "bvxor")

    def walk_bv_xnor(self, formula, args):
        return self.walk_nary(formula, args, "bvxnor")

    def walk_bv_add(self, formula, args):
        return self.walk_nary(formula, args, "bvadd")

    def walk_bv_sub(self, formula, args):
        return self.walk_nary(formula, args, "bvsub")

    def walk_bv_neg(self, formula, args):
        return self.walk_nary(formula, args, "bvneg")

    def walk_bv_mul(self, formula, args):
        return self.walk_nary(formula, args, "bvmul")

    def walk_bv_udiv(self, formula, args):
        return self.walk_nary(formula, args, "bvudiv")

    def walk_bv_urem(self, formula, args):
        return self.walk_nary(formula, args, "bvurem")

    def walk_bv_lshl(self, formula, args):
        return self.walk_nary(formula, args, "bvshl")

    def walk_bv_lshr(self, formula, args):
        return self.walk_nary(formula, args, "bvlshr")

    def walk_bv_ult(self, formula, args):
        return self.walk_nary(formula, args, "bvult")

    def walk_bv_ugt(self, formula, args):
        return self.walk_nary(formula, args, "bvugt")

    def walk_bv_ule(self, formula, args):
        return self.walk_nary(formula, args, "bvule")

    def walk_bv_uge(self, formula, args):
        return self.walk_nary(formula, args, "bvuge")

    def walk_bv_slt(self, formula, args):
        return self.walk_nary(formula, args, "bvslt")

    def walk_bv_sle(self, formula, args):
        return self.walk_nary(formula, args, "bvsle")

    def walk_bv_concat(self, formula, args):
        return self.walk_nary(formula, args, "concat")

    def walk_bv_comp(self, formula, args):
        return self.walk_nary(formula, args, "bvcomp")

    def walk_bv_ashr(self, formula, args):
        return self.walk_nary(formula, args, "bvashr")

    def walk_bv_sdiv(self, formula, args):
        return self.walk_nary(formula, args, "bvsdiv")

    def walk_bv_srem(self, formula, args):
        return self.walk_nary(formula, args, "bvsrem")

    def walk_bv_smod(self, formula, args):
        return self.walk_nary(formula, args, "bvsmod")

    def walk_bv_tonatural(self, formula, args):
        return self.walk_nary(formula, args, "bv2nat")

    def walk_bv_to_int(self, formula, args):
        return self.walk_nary(formula, args, "bv2int")

    def walk_array_select(self, formula, args):
        return self.walk_nary(formula, args, "select")

    def walk_array_store(self, formula, args):
        return self.walk_nary(formula, args, "store")

    def walk_symbol(self, formula, **kwargs):
        return quote(formula.symbol_name())

    def walk_function(self, formula, args, **kwargs):
        return self.walk_nary(
            formula, args, quote(formula.function_name().symbol_name())
        )

    def walk_int_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            return "(- " + str(-formula.constant_value()) + ")"
        else:
            return str(formula.constant_value())

    def walk_real_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        constant_value = formula.constant_value()

        if is_pysmt_fraction(constant_value):
            (n, d) = (
                abs(formula.constant_value().numerator),
                formula.constant_value().denominator,
            )
            if d != 1:
                # print as decimal
                # set very large precision
                getcontext().prec = 999_999
                d = Decimal(n) / Decimal(d)
                res = template % str(d)
            else:
                res = template % (str(n) + ".0")
        else:
            # use default encoding of the value type
            res = str(abs(constant_value))
            if "." not in res:
                res += ".0"
            res = template % res

        return res

    def walk_bv_constant(self, formula, **kwargs):
        short_res = str(bin(formula.constant_value()))[2:]
        if formula.constant_value() >= 0:
            filler = "0"
        else:
            raise NotImplementedError
        res = short_res.rjust(formula.bv_width(), filler)
        return "#b" + res

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return "true"
        else:
            return "false"

    def walk_str_constant(self, formula, **kwargs):
        if formula.str_unary_hex():
            # turn character into hex
            c = formula.constat_value()
            c_hex = hex(ord(c)).replace("0x", "#x")
            return f"(_ char {c_hex})"

        return '"' + formula.constant_value().replace('"', '""') + '"'

    def walk_forall(self, formula, args, **kwargs):
        return self._walk_quantifier("forall", formula, args)

    def walk_exists(self, formula, args, **kwargs):
        return self._walk_quantifier("exists", formula, args)

    def _walk_quantifier(self, operator, formula, args):
        assert args is None
        assert len(formula.quantifier_vars()) > 0
        sym = self._new_symbol()
        self.openings += 1

        self.write("(let ((%s (%s (" % (sym, operator))

        for s in formula.quantifier_vars():
            self.write("(")
            self.write(quote(s.symbol_name()))
            self.write(" %s)" % s.symbol_type().as_smtlib(False))
        self.write(") ")

        subprinter = SmtDagPrinter(self.stream)
        subprinter.printer(formula.arg(0), name_seed=self.name_seed)
        self.name_seed = subprinter.name_seed

        self.write("))) ")
        return sym

    def walk_bv_extract(self, formula, args, **kwargs):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        self.write(
            "(let ((%s ((_ extract %d %d)"
            % (sym, formula.bv_extract_end(), formula.bv_extract_start())
        )
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    @handles(op.BV_SEXT, op.BV_ZEXT)
    def walk_bv_extend(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        if formula.is_bv_zext():
            extend_type = "zero_extend"
        else:
            assert formula.is_bv_sext()
            extend_type = "sign_extend"

        sym = self._new_symbol()
        self.openings += 1
        self.write(
            "(let ((%s ((_ %s %d)" % (sym, extend_type, formula.bv_extend_step())
        )
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    @handles(op.BV_ROR, op.BV_ROL)
    def walk_bv_rotate(self, formula, args, **kwargs):
        # pylint: disable=unused-argument
        if formula.is_bv_ror():
            rotate_type = "rotate_right"
        else:
            assert formula.is_bv_rol()
            rotate_type = "rotate_left"

        sym = self._new_symbol()
        self.openings += 1
        self.write(
            "(let ((%s ((_ %s %d)" % (sym, rotate_type, formula.bv_rotation_step())
        )
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_str_length(self, formula, args, **kwargs):
        return "(str.len %s)" % args[0]

    def walk_str_charat(self, formula, args, **kwargs):
        return "( str.at %s %s )" % (args[0], args[1])

    def walk_str_concat(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "str.++ "))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_str_contains(self, formula, args, **kwargs):
        return "( str.contains %s %s)" % (args[0], args[1])

    def walk_str_indexof(self, formula, args, **kwargs):
        return "( str.indexof %s %s %s )" % (args[0], args[1], args[2])

    def walk_str_replace(self, formula, args, **kwargs):
        return "( str.replace %s %s %s )" % (args[0], args[1], args[2])

    def walk_str_replace_all(self, formula, args, **kwargs):
        return "( str.replace_all %s %s %s )" % (args[0], args[1], args[2])

    def walk_str_substr(self, formula, args, **kwargs):
        return "( str.substr %s %s %s)" % (args[0], args[1], args[2])

    def walk_str_prefixof(self, formula, args, **kwargs):
        return "( str.prefixof %s %s )" % (args[0], args[1])

    def walk_str_suffixof(self, formula, args, **kwargs):
        return "( str.suffixof %s %s )" % (args[0], args[1])

    def walk_str_to_int(self, formula, args, **kwargs):
        return "( str.to_int %s )" % args[0]

    def walk_str_to_re(self, formula, args, **kwargs):
        return "( str.to_re %s )" % args[0]

    def walk_str_in_re(self, formula, args, **kwargs):
        return "( str.in_re %s %s )" % (args[0], args[1])

    def walk_str_replace_re(self, formula, args, **kwargs):
        return "( str.replace_re %s %s %s )" % (args[0], args[1], args[2])

    def walk_str_compare(self, formula, args, **kwargs):
        return "( str.<= %s %s )" % (args[0], args[1])

    def walk_str_replace_re_all(self, formula, args, **kwargs):
        return "( str.replace_re_all %s %s %s )" % (args[0], args[1], args[2])

    def walk_re_all(self, formula, args, **kwargs):
        return "re.all"

    def walk_re_allchar(self, formula, args, **kwargs):
        return "re.allchar"

    def walk_re_none(self, formula, args, **kwargs):
        return "re.none"

    def walk_re_concat(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "re.++ "))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_re_inter(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "re.inter "))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_re_union(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "re.union "))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_re_star(self, formula, args, **kwargs):
        return "( re.* %s )" % args[0]

    def walk_re_comp(self, formula, args, **kwargs):
        return "( re.comp %s )" % args[0]

    def walk_re_diff(self, formula, args, **kwargs):
        return "( re.diff %s %s )" % (args[0], args[1])

    def walk_re_plus(self, formula, args, **kwargs):
        return "( re.+ %s )" % args[0]

    def walk_re_opt(self, formula, args, **kwargs):
        return "( re.opt %s )" % args[0]

    def walk_re_range(self, formula, args, **kwargs):
        return "( re.range %s %s )" % (args[0], args[1])

    def walk_re_power(self, formula, args, **kwargs):
        exponent = formula.re_power_exponent()
        return "( (_ re.^ %s) %s )" % (exponent, args[0])

    def walk_re_loop(self, formula, args, **kwargs):
        lb, ub = formula.re_loop_bounds()
        return "( (_ re.loop %s %s) %s )" % (lb, ub, args[0])

    def walk_rne(self, formula, args, **kwargs):
        return "RNE"

    def walk_rna(self, formula, args, **kwargs):
        return "RNA"

    def walk_rtp(self, formula, args, **kwargs):
        return "RTP"

    def walk_rtn(self, formula, args, **kwargs):
        return "RTN"

    def walk_rtz(self, formula, args, **kwargs):
        return "RTZ"

    def walk_int_to_str(self, formula, args, **kwargs):
        return "( str.from_int %s )" % args[0]

    def walk_array_value(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s " % sym)

        for _ in range((len(args) - 1) // 2):
            self.write("(store ")

        self.write("((as const %s) " % formula.get_type().as_smtlib(False))
        self.write(args[0])
        self.write(")")

        for i, k in enumerate(args[1::2]):
            self.write(" ")
            self.write(k)
            self.write(" ")
            self.write(args[2 * i + 2])
            self.write(")")
        self.write("))")
        return sym

    def walk_re_concat(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "re.++ "))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym


    def walk_is(self, formula, args):
        sym = self._new_symbol()

        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "(_ is "))

        self.write(self.memoization[formula.constructor()])
        self.write(") ")
        self.write(args[0])
        self.write(")))")
        return sym


    def walk_int_to_bv(self, formula, args):
        sym = self._new_symbol()

        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "(_ int2bv "))
        self.write(str(formula.bv_width()))
        self.write(") ")
        self.write(args[0])
        self.write(")")
        return sym


def to_smtlib(formula, daggify=True):
    """Returns a Smt-Lib string representation of the formula.

    The daggify parameter can be used to switch from a linear-size
    representation that uses 'let' operators to represent the
    formula as a dag or a simpler (but possibly exponential)
    representation that expands the formula as a tree.

    See :py:class:`SmtPrinter`
    """
    buf = StringIO()
    p = None
    if daggify:
        p = SmtDagPrinter(buf)
    else:
        p = SmtPrinter(buf)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    return res
