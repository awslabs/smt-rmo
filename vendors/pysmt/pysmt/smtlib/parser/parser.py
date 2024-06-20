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
import functools
from io import StringIO
import itertools

from warnings import warn
from collections import deque

import pysmt.smtlib.commands as smtcmd
from pysmt.environment import get_env, reset_env
from pysmt.logics import get_logic_by_name, UndefinedLogicError
from pysmt.exceptions import UnknownSmtLibCommandError, PysmtSyntaxError
from pysmt.exceptions import PysmtTypeError
from pysmt.smtlib.script import SmtLibCommand, SmtLibScript
from pysmt.utils import ImmutableAnnotations, interactive_char_iterator, quote
from pysmt.constants import Fraction
from pysmt.typing import _TypeDecl, PartialType, ADT, FunctionType
from pysmt.substituter import FunctionInterpretation
import sys
from decimal import Decimal, getcontext


def open_(fname):
    """Transparently handle .bz2 files."""
    if fname.endswith(".bz2"):
        import bz2

        return bz2.open(fname, "rt")
    return open(fname)


def get_formula(script_stream, environment=None):
    """
    Returns the formula asserted at the end of the given script

    script_stream is a file descrpiptor.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = SmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_last_formula(mgr)


def get_formula_strict(script_stream, environment=None):
    """Returns the formula defined in the SMTScript.

    This function assumes that only one formula is defined in the
    SMTScript. It will raise an exception if commands such as pop and
    push are present in the script, or if check-sat is called more
    than once.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = SmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_strict_formula(mgr)


def get_formula_fname(script_fname, environment=None, strict=True):
    """Returns the formula asserted at the end of the given script."""
    with open_(script_fname) as script:
        if strict:
            return get_formula_strict(script, environment)
        else:
            return get_formula(script, environment)


class SmtLibExecutionCache(object):
    """Execution environment for SMT2 script execution"""

    def __init__(self, env):
        self.substitute = env.substituter.substitute
        self.keys = {}
        self.definitions = {}

    def bind(self, name, value):
        """Binds a symbol in this environment"""
        lst = self.keys.setdefault(name, [])
        lst.append(value)

    def unbind(self, name):
        """Unbinds the last binding of this symbol"""
        self.keys[name].pop()

    def define(self, name, parameters, expression):
        self.definitions[name] = (parameters, expression)

    def _define_adapter(self, formal_parameters, expression):
        def res(*actual_parameters):
            assert len(formal_parameters) == len(actual_parameters)
            submap = dict(zip(formal_parameters, actual_parameters))
            return self.substitute(expression, submap)

        return res

    def get(self, name):
        res = self._get(name)
        if name[0] == "|" and name[-1] == "|":
            name2 = name[1:-1]
        else:
            name2 = "|" + name + "|"

        if res is None:
            return self._get(name2)

        return res

    def _get(self, name):
        """Returns the last binding for 'name'"""
        if name in self.definitions:
            (parameters, expression) = self.definitions[name]
            if len(parameters) == 0:
                return expression
            return self._define_adapter(parameters, expression)
        elif name in self.keys:
            lst = self.keys[name]
            if len(lst) > 0:
                return lst[-1]
            else:
                return None
        else:
            return None

    def update(self, value_map):
        """Binds all the symbols in 'value_map'"""
        for k, val in value_map.items():
            self.bind(k, val)

    def unbind_all(self, values):
        """UnBinds all the symbols in 'values'"""
        for k in values:
            self.unbind(k)


# EOC SmtLibExecutionCache


class Tokenizer(object):
    """Takes a file-like object and produces a stream of tokens following
    the LISP rules.

    If interactive is True, the file reading proceeds char-by-char with
    no buffering. This is useful for interactive use for example with
    a SMT-Lib2-compliant solver

    The method add_extra_token allows to "push-back" a token, so that
    it will be returned by the next call to consume_token, instead of
    reading from the actual generator.

    """

    def __init__(self, handle, interactive=False):
        if not interactive:
            # reads char-by-char
            if __debug__:
                self.reader = self.char_iterator(handle)
                self.__col_cnt = 0
                self.__row_cnt = 0
            else:
                self.reader = itertools.chain.from_iterable(handle)
                self.__col_cnt = None
                self.__row_cnt = None
        else:
            self.reader = interactive_char_iterator(handle)
            self.__col_cnt = None
            self.__row_cnt = None
        self.generator = self.create_generator(self.reader)
        self.extra_queue = deque()
        self._include_pipes = True

    def add_extra_token(self, token):
        self.extra_queue.append(token)

    def consume_maybe(self, include_pipes=None):
        """Consumes and returns a single token from the stream.
        If the stream is empty `StopIteration` is thrown"""
        if self.extra_queue:
            return self.extra_queue.popleft()
        else:
            old_include_pipes = self._include_pipes
            self._include_pipes = (
                include_pipes if include_pipes is not None else self._include_pipes
            )
            res = next(self.generator)
            self._include_pipes = old_include_pipes
            return res

    def consume(self, msg=None, include_pipes=False):
        """Consumes and returns a single token from the stream.
        If the stream is empty, a PysmtSyntaxError is thrown"""
        if self.extra_queue:
            return self.extra_queue.popleft()
        else:
            try:
                t = self.consume_maybe(include_pipes=include_pipes)
            except StopIteration:
                if msg:
                    raise PysmtSyntaxError(msg, self.pos_info)
                else:
                    raise PysmtSyntaxError("Unexpected end of stream.", self.pos_info)
            return t

    def raw_read(self):
        return next(self.reader)

    def seek_back_raw(self, offset):
        """Seeks back the reader by offset chars"""
        assert offset >= 0
        if offset > 0:
            current_pos = self.reader.tell()
            self.reader.seek(current_pos - offset)

    @property
    def pos_info(self):
        if self.__row_cnt is not None:
            return (self.__row_cnt, self.__col_cnt)
        return None

    # @staticmethod
    def create_generator(self, reader):
        """Takes a file-like object and produces a stream of tokens following
        the LISP rules.

        This is the method doing the heavy-lifting of tokenization.
        """
        spaces = set([" ", "\n", "\t"])
        separators = set(["(", ")", "|", '"'])
        specials = spaces | separators | set([";", ""])

        try:
            c = next(reader)
            eof = False
            while not eof:
                if c in specials:
                    # consume the spaces
                    if c in spaces:
                        c = next(reader)

                    elif c in separators:
                        if c == "|":
                            s = []
                            c = next(reader)
                            while c and c != "|":
                                if c == "\\":  # This is a single '\'
                                    c = next(reader)
                                    if c != "|" and c != "\\":
                                        # Only \| and \\ are supported escapings
                                        raise PysmtSyntaxError(
                                            "Unknown escaping in quoted symbol: "
                                            "'\\%s'" % c,
                                            reader.pos_info,
                                        )
                                s.append(c)
                                c = next(reader)
                            if not c:
                                raise PysmtSyntaxError("Expected '|'", reader.pos_info)
                            res = "".join(s)
                            if self._include_pipes:
                                res = "|" + res + "|"
                            yield res
                            c = next(reader)

                        elif c == '"':
                            # String literals
                            s = c
                            num_quotes = 0
                            while True:
                                c = next(reader)
                                if not c:
                                    raise PysmtSyntaxError(
                                        "Expected '\"'", reader.pos_info
                                    )

                                if c != '"' and num_quotes % 2 != 0:
                                    break

                                s += c
                                if c == '"':
                                    num_quotes += 1

                            yield s

                        else:
                            yield c
                            c = next(reader)

                    elif c == ";":
                        while c and c != "\n":
                            c = next(reader)
                        c = next(reader)

                    else:
                        # EOF
                        eof = True
                        assert len(c) == 0
                else:
                    tk = []
                    while c not in specials:
                        tk.append(c)
                        c = next(reader)
                    yield "".join(tk)
        except StopIteration:
            # No more data to read, close generator
            return

    def char_iterator(self, handle):
        c = handle.read(1)
        while c:
            if c == "\n":
                self.__row_cnt += 1
                self.__col_cnt = 0
            elif c == "\r":
                pass
            else:
                self.__col_cnt += 1
            yield c
            c = handle.read(1)


# EOC Tokenizer


class SmtLibParser(object):
    """Parse an SmtLib file and builds an SmtLibScript object.

    The main function is get_script (and its wrapper
    get_script_fname).  This function relies on the tokenizer function
    (to split the inputs in token) that is consumed by the get_command
    function that returns a SmtLibCommand for each command in the
    original file.

    If the interactive flag is True, the file reading proceeds
    char-by-char with no buffering. This is useful for interactive use
    for example with a SMT-Lib2-compliant solver
    """

    def __init__(self, environment=None, interactive=False, expand_let=False):
        # deal with gigantic numbers
        sys.set_int_max_str_digits(999_999)

        self.env = get_env() if environment is None else environment
        self.interactive = interactive

        # Placeholders for fields filled by self._reset
        self.cache = None
        self.logic = None
        self._anonymous_vars_counter = 0
        self._reset()

        mgr = self.env.formula_manager

        # Fixing the issue with integer/real numbers on arithmetic
        # operators.
        #
        # We try to apply the operator as it is, in case of failure,
        # we try to interpret as reals the constant operands that are
        # integers
        def fix_real(op, *args):
            try:
                return op(*args)
            except PysmtTypeError:
                get_type = self.env.stc.get_type
                get_free_variables = self.env.fvo.get_free_variables
                new_args = []
                for x in args:
                    if get_type(x).is_int_type():
                        new_args.append(mgr.ToReal(x))
                    else:
                        new_args.append(x)
                if args == new_args:
                    raise
                return op(*new_args)

        self.LT = functools.partial(fix_real, mgr.LT)
        self.GT = functools.partial(fix_real, mgr.GT)
        self.LE = functools.partial(fix_real, mgr.LE)
        self.GE = functools.partial(fix_real, mgr.GE)
        self.Equals = functools.partial(fix_real, mgr.Equals)
        self.EqualsOrIff = functools.partial(fix_real, mgr.EqualsOrIff)
        self.Plus = functools.partial(fix_real, mgr.Plus)
        self.Minus = functools.partial(fix_real, mgr.Minus)
        self.Times = functools.partial(fix_real, mgr.Times)
        self.Div = functools.partial(fix_real, mgr.Div)
        self.Ite = functools.partial(fix_real, mgr.Ite)
        self.AllDifferent = functools.partial(fix_real, mgr.AllDifferent)

        # Tokens representing interpreted functions appearing in expressions
        # Each token is handled by a dedicated function that takes the
        # recursion stack, the token stream and the parsed token
        # Common tokens are handled in the _reset function
        self.interpreted = {
            "let": self._enter_let_expand if expand_let else self._enter_let,
            "!": self._enter_annotation,
            "exists": self._enter_quantifier,
            "forall": self._enter_quantifier,
            "+": self._operator_adapter(self.Plus),
            "-": self._operator_adapter(self._minus_or_uminus),
            "*": self._operator_adapter(self.Times),
            "/": self._operator_adapter(self._division),
            "div": self._operator_adapter(
                mgr.FloorDiv
            ),  # TODO: check if operator overloaded for BVs
            "mod": self._operator_adapter(
                mgr.Mod
            ),  # TODO: check if operator overloaded for BVs
            "abs": self._operator_adapter(mgr.Abs),
            "pow": self._operator_adapter(mgr.Pow),
            ">": self._operator_adapter(self.GT),
            "<": self._operator_adapter(self.LT),
            ">=": self._operator_adapter(self.GE),
            "<=": self._operator_adapter(self.LE),
            "=": self._operator_adapter(self._equals_or_iff),
            "not": self._operator_adapter(mgr.Not),
            "and": self._operator_adapter(mgr.And),
            "or": self._operator_adapter(mgr.Or),
            "xor": self._operator_adapter(mgr.Xor),
            "=>": self._operator_adapter(mgr.Implies),
            # this is not SMTLIB compliant
            # '<->':self._operator_adapter(mgr.Iff),
            "ite": self._operator_adapter(self.Ite),
            "distinct": self._operator_adapter(self.AllDifferent),
            "to_real": self._operator_adapter(mgr.ToReal),
            "to_int": self._operator_adapter(mgr.RealToInt),
            "concat": self._operator_adapter(mgr.BVConcat),
            "bvnot": self._operator_adapter(mgr.BVNot),
            "bvand": self._operator_adapter(mgr.BVAnd),
            "bvnand": self._operator_adapter(mgr.BVNand),
            "bvor": self._operator_adapter(mgr.BVOr),
            "bvnor": self._operator_adapter(mgr.BVNor),
            "bvneg": self._operator_adapter(mgr.BVNeg),
            "bvadd": self._operator_adapter(mgr.BVAdd),
            "bvmul": self._operator_adapter(mgr.BVMul),
            "bvudiv": self._operator_adapter(mgr.BVUDiv),
            "bvurem": self._operator_adapter(mgr.BVURem),
            "bvshl": self._operator_adapter(mgr.BVLShl),
            "bvlshr": self._operator_adapter(mgr.BVLShr),
            "bvsub": self._operator_adapter(mgr.BVSub),
            "bvult": self._operator_adapter(mgr.BVULT),
            "bvugt": self._operator_adapter(mgr.BVUGT),
            "bvxor": self._operator_adapter(mgr.BVXor),
            "_": self._smtlib_underscore,
            # Extended Functions
            "bvnand": self._operator_adapter(mgr.BVNand),
            "bvnor": self._operator_adapter(mgr.BVNor),
            "bvxnor": self._operator_adapter(mgr.BVXnor),
            "bvcomp": self._operator_adapter(mgr.BVComp),
            "bvsdiv": self._operator_adapter(mgr.BVSDiv),
            "bvsrem": self._operator_adapter(mgr.BVSRem),
            "bvsmod": self._operator_adapter(mgr.BVSMod),
            "bvashr": self._operator_adapter(mgr.BVAShr),
            "bvule": self._operator_adapter(mgr.BVULE),
            "bvuge": self._operator_adapter(mgr.BVUGE),
            "bvslt": self._operator_adapter(mgr.BVSLT),
            "bvsle": self._operator_adapter(mgr.BVSLE),
            "bvsgt": self._operator_adapter(mgr.BVSGT),
            "bvsge": self._operator_adapter(mgr.BVSGE),
            # Strings
            "str.len": self._operator_adapter(mgr.StrLength),
            "str.++": self._operator_adapter(mgr.StrConcat),
            "str.at": self._operator_adapter(mgr.StrCharAt),
            "str.contains": self._operator_adapter(mgr.StrContains),
            "str.indexof": self._operator_adapter(mgr.StrIndexOf),
            "str.replace": self._operator_adapter(mgr.StrReplace),
            "str.replace_all": self._operator_adapter(mgr.StrReplaceAll),
            "str.substr": self._operator_adapter(mgr.StrSubstr),
            "str.prefixof": self._operator_adapter(mgr.StrPrefixOf),
            "str.suffixof": self._operator_adapter(mgr.StrSuffixOf),
            # old, cvc4 syntax
            "str.to.int": self._operator_adapter(mgr.StrToInt),
            "int.to.str": self._operator_adapter(mgr.IntToStr),
            # smtlib 2.6
            "str.to_int": self._operator_adapter(mgr.StrToInt),
            "str.from_int": self._operator_adapter(mgr.IntToStr),
            #
            "bv2nat": self._operator_adapter(mgr.BVToNatural),
            "bv2int": self._operator_adapter(mgr.BVToInt),
            # arrays
            "select": self._operator_adapter(mgr.Select),
            "store": self._operator_adapter(mgr.Store),
            "as": self._enter_smtlib_as,
            "str.to_re": self._operator_adapter(mgr.StrToRe),
            "str.in_re": self._operator_adapter(mgr.StrInRe),
            "str.<=": self._operator_adapter(mgr.StrCompare),
            "str.replace_re": self._operator_adapter(mgr.StrReplaceRe),
            "str.replace_re_all": self._operator_adapter(mgr.StrReplaceReAll),
            "re.all": self._operator_adapter(mgr.ReAll),
            "re.allchar": self._operator_adapter(mgr.ReAllChar),
            "re.none": self._operator_adapter(mgr.ReNone),
            "re.++": self._operator_adapter(mgr.ReConcat),
            "re.inter": self._operator_adapter(mgr.ReInter),
            "re.union": self._operator_adapter(mgr.ReUnion),
            "re.*": self._operator_adapter(mgr.ReStar),
            "re.comp": self._operator_adapter(mgr.ReComp),
            "re.diff": self._operator_adapter(mgr.ReDiff),
            "re.+": self._operator_adapter(mgr.RePlus),
            "re.opt": self._operator_adapter(mgr.ReOpt),
            "re.range": self._operator_adapter(mgr.ReRange),
            "re.^": self._operator_adapter(mgr.RePower),
            "re.loop": self._operator_adapter(mgr.ReLoop),
            "RNE": self._operator_adapter(mgr.RNE),
            "RNA": self._operator_adapter(mgr.RNA),
            "RTP": self._operator_adapter(mgr.RTP),
            "RTN": self._operator_adapter(mgr.RTN),
            "RTZ": self._operator_adapter(mgr.RTZ),
        }

        # Command tokens
        self.commands = {
            smtcmd.ASSERT: self._cmd_assert,
            smtcmd.CHECK_SAT: self._cmd_check_sat,
            smtcmd.CHECK_SAT_ASSUMING: self._cmd_check_sat_assuming,
            smtcmd.DECLARE_CONST: self._cmd_declare_const,
            smtcmd.DECLARE_FUN: self._cmd_declare_fun,
            smtcmd.DECLARE_SORT: self._cmd_declare_sort,
            smtcmd.DEFINE_FUN: self._cmd_define_fun,
            smtcmd.DEFINE_FUNS_REC: self._cmd_define_funs_rec,
            smtcmd.DEFINE_FUN_REC: self._cmd_define_fun_rec,
            smtcmd.DEFINE_SORT: self._cmd_define_sort,
            smtcmd.ECHO: self._cmd_echo,
            smtcmd.EXIT: self._cmd_exit,
            smtcmd.GET_ASSERTIONS: self._cmd_get_assertions,
            smtcmd.GET_ASSIGNMENT: self._cmd_get_assignment,
            smtcmd.GET_INFO: self._cmd_get_info,
            smtcmd.GET_MODEL: self._cmd_get_model,
            smtcmd.GET_OPTION: self._cmd_get_option,
            smtcmd.GET_PROOF: self._cmd_get_proof,
            smtcmd.GET_UNSAT_ASSUMPTIONS: self._cmd_get_unsat_assumptions,
            smtcmd.GET_UNSAT_CORE: self._cmd_get_unsat_core,
            smtcmd.GET_VALUE: self._cmd_get_value,
            smtcmd.POP: self._cmd_pop,
            smtcmd.PUSH: self._cmd_push,
            smtcmd.RESET: self._cmd_reset,
            smtcmd.RESET_ASSERTIONS: self._cmd_reset_assertions,
            smtcmd.SET_LOGIC: self._cmd_set_logic,
            smtcmd.SET_OPTION: self._cmd_set_option,
            smtcmd.SET_INFO: self._cmd_set_info,
            #
            smtcmd.DECLARE_DATATYPE: self._cmd_declare_datatype,
            smtcmd.DECLARE_DATATYPES: self._cmd_declare_multiple_datatypes,
        }

    def _reset(self):
        """Resets the parser to the initial state"""
        self.cache = SmtLibExecutionCache(self.env)
        self.logic = None
        mgr = self.env.formula_manager
        self.cache.update({"false": mgr.FALSE(), "true": mgr.TRUE()})

    def _minus_or_uminus(self, *args):
        """Utility function that handles both unary and binary minus"""
        mgr = self.env.formula_manager
        if len(args) == 1:
            lty = self.env.stc.get_type(args[0])
            mult = None
            if lty == self.env.type_manager.INT():
                if args[0].is_int_constant():
                    return mgr.Int(-1 * args[0].constant_value())
                mult = mgr.Int(-1)
            else:
                if args[0].is_real_constant():
                    return mgr.Real(-1 * args[0].constant_value())
                mult = mgr.Real(-1)
            return mgr.Times(mult, args[0])
        else:
            assert len(args) == 2
            return self.Minus(args[0], args[1])

    def _enter_smtlib_as(self, stack, tokens, key):
        """Utility function that handles 'as' that is a special function in SMTLIB"""
        # pylint: disable=unused-argument
        what = self.parse_atom(tokens, "expression")
        ty = self.parse_type(tokens, "expression")
        if what == "const":
            assert (
                ty.is_array_type()
            ), "(as const x) is supported only for array constants"

            def res(expr):
                return self.env.formula_manager.Array(ty.index_type, expr)

            def handler():
                return res

            stack[-1].append(handler)
        else:

            def handler():
                return self.env.formula_manager.Symbol(what, ty)

            stack[-1].append(handler)

    def _smtlib_underscore(self, stack, tokens, key):
        # pylint: disable=unused-argument
        """Utility function that handles _ special function in SMTLIB"""
        mgr = self.env.formula_manager

        op = self.parse_atom(tokens, "expression")

        fun = None
        if op == "extract":
            send = self.parse_atom(tokens, "expression")
            sstart = self.parse_atom(tokens, "expression")
            try:
                start = int(sstart)
                end = int(send)
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '_ extract' " "expression", tokens.pos_info
                )
            fun = lambda x: mgr.BVExtract(x, start, end)

        elif op == "zero_extend":
            swidth = self.parse_atom(tokens, "expression")
            try:
                width = int(swidth)
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '_ zero_extend' " "expression", tokens.pos_info
                )
            fun = lambda x: mgr.BVZExt(x, width)

        elif op == "repeat":
            scount = self.parse_atom(tokens, "expression")
            try:
                count = int(scount)
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '_ repeat' " "expression", tokens.pos_info
                )
            fun = lambda x: mgr.BVRepeat(x, count)

        elif op == "rotate_left":
            sstep = self.parse_atom(tokens, "expression")
            try:
                step = int(sstep)
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '_ rotate_left' " "expression", tokens.pos_info
                )
            fun = lambda x: mgr.BVRol(x, step)

        elif op == "rotate_right":
            sstep = self.parse_atom(tokens, "expression")
            try:
                step = int(sstep)
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '_ rotate_left' " "expression", tokens.pos_info
                )
            fun = lambda x: mgr.BVRor(x, step)

        elif op == "sign_extend":
            swidth = self.parse_atom(tokens, "expression")
            try:
                width = int(swidth)
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '(_ sign_extend) " "expression'",
                    tokens.pos_info,
                )
            fun = lambda x: mgr.BVSExt(x, width)

        elif op.startswith("bv"):
            try:
                v = int(op[2:])
                width = int(self.parse_atom(tokens, "expression"))
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected number in '_ bv' expression: " "'%s'" % op,
                    tokens.pos_info,
                )
            fun = mgr.BV(v, width, underscore=True)

        elif op == "re.loop":
            lb = self.parse_atom(tokens, "expression")
            ub = self.parse_atom(tokens, "expression")
            try:
                lb = int(lb)
                ub = int(ub)
                if lb < 0 or ub < 0:
                    raise ValueError
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected natural constants in '_ re.loop' " "expression",
                    tokens.pos_info,
                )
            fun = lambda r: mgr.ReLoop(r, lb, ub)

        elif op == "re.^":
            n = self.parse_atom(tokens, "expression")
            try:
                n = int(n)
                if n < 0:
                    raise ValueError
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected natural constants in '_ re.^' " "expression",
                    tokens.pos_info,
                )
            fun = lambda r: mgr.RePower(r, n)

        elif op == "is":
            constructor = self.parse_atom(tokens, "expression")
            try:
                constructor = self.atom(constructor, tokens, mgr)
            except:
                raise PysmtSyntaxError("is argument unexpected", tokens.pos_info)
            fun = lambda r: mgr.Is(constructor, r)

        elif op == "int2bv":
            n = self.parse_atom(tokens, "expression")
            try:
                n = int(n)
                if n <= 0:
                    raise ValueError
            except ValueError:
                raise PysmtSyntaxError(
                    "Expected int > 0 constants in '_ int2bv' " "expression",
                    tokens.pos_info,
                )
            fun = lambda r: mgr.IntToBV(r, n)


        elif op == "char":
            c_hex = self.parse_atom(tokens, "expression")
            print (c_hex)
            if "#x" not in c_hex:
                return PysmtSyntaxError(f"char expects a hexadecimal; recieved, {c_hex}" , tokens.pos_info)
            fun = mgr.String(c_hex,unary_hex=True)
            
        else:
            raise PysmtSyntaxError(
                "Unexpected '_' expression '%s'" % op, tokens.pos_info
            )

        stack[-1].append(lambda: fun)

    def _equals_or_iff(self, left, right):
        """Utility function that treats = between booleans as <->"""
        mgr = self.env.formula_manager
        lty = self.env.stc.get_type(left)
        if lty == self.env.type_manager.BOOL():
            return mgr.Iff(left, right)
        else:
            return self.Equals(left, right)

    def _division(self, left, right):
        """Utility function that builds a division"""
        return self.Div(left, right)

    def _get_var(self, name, type_name):
        """Returns the PySMT variable corresponding to a declaration"""
        return self.env.formula_manager.Symbol(name=name, typename=type_name)

    def _get_quantified_var(self, name, type_name, prefix="qv"):
        """Returns the PySMT variable corresponding to a declaration"""
        # try:
        #     return self._get_var(name, type_name)
        # except PysmtTypeError:
        # From now on, we will use fresh symbols for quantified and let variables
        return self.env.formula_manager.FreshSymbol(
            typename=type_name, template=prefix + "_%d"
        )

    def atom(self, token, tokens, mgr):
        """
        Given a token and a FormulaManager, returns the pysmt representation of
        the token
        """
        # In principle, a variable may be called |42|, i.e., when enclosed between
        # pipes, a number can be interpreted as a valid identifier. As a workaround,
        # we first try to parse the tocken as Decimal. If the parsing fail, we look
        # at the cache for an identifier having the name |tocken|
        try:
            Decimal(token)
            res = None
        except:
            res = self.cache.get(token)

        if res is None:
            if token.startswith("#"):
                # it is a BitVector
                value = None
                width = None
                if token[1] == "b":
                    # binary
                    width = len(token) - 2
                    value = int("0" + token[1:], 2)
                    hexadecimal = False
                else:
                    if token[1] != "x":
                        raise PysmtSyntaxError(
                            "Invalid bit-vector constant " "'%s'" % token,
                            tokens.pos_info
                        )
                    width = (len(token) - 2) * 4
                    value = int("0" + token[1:], 16)
                    hexadecimal = True
                res = mgr.BV(value, width, hexadecimal=hexadecimal)
            elif token[0] == '"':
                # String constant
                val = token[1:-1]
                val = val.replace('""', '"')
                res = mgr.String(val)
            elif token == "re.all":
                res = mgr.ReAll()
            elif token == "re.allchar":
                res = mgr.ReAllChar()
            elif token == "re.none":
                res = mgr.ReNone()
            else:
                # it must be a number
                try:
                    # `fractions` library cannot handle large strings due to a bug in its impl
                    # FIX: parse as decimal first
                    # high precision just in case of ridiculous inputs
                    getcontext().prec = 999_999
                    try:
                        dec = Decimal(token)
                    except:
                        raise PysmtSyntaxError(
                            f"Expected numeric literal but got {str(token)}"
                        )
                    num, denom = dec.as_integer_ratio()
                    frac = Fraction(num, denom)

                    if frac.denominator == 1:
                        # We found an integer, depending on the logic this can be
                        # an Int or a Real
                        if self.logic is None or self.logic.theory.integer_arithmetic:
                            if "." in token:
                                res = mgr.Real(frac.numerator)  # original
                            else:
                                res = mgr.Int(frac.numerator)
                        else:
                            # res = mgr.Real(frac) # original
                            res = mgr.Real(frac.numerator)
                    else:
                        res = mgr.Real(frac)
                except Exception as e:
                    raise PysmtSyntaxError(f"did not expect {token}", tokens.pos_info) from e

            self.cache.bind(token, res)
        return res

    def _exit_quantifier(self, fun, vrs, body):
        """
        Cleans the execution environment when we exit the scope of a quantifier
        """
        variables = set()
        for vname, var in vrs:
            self.cache.unbind(vname)
            variables.add(var)
        return fun(variables, body)

    def _exit_let(self, varlist, expressionlist, bdy):
        """Cleans the execution environment when we exit the scope of a 'let'"""
        mgr = self.env.formula_manager
        variables = []

        for k, v in varlist:
            self.cache.unbind(k)
            variables.append(v)

        return mgr.Let(variables, expressionlist, bdy)

    def _unique_anonymous_var_id(self) -> str:
        res = self._anonymous_vars_counter
        self._anonymous_vars_counter += 1
        return str(res)

    def _enter_let_expand(self, stack, tokens, key):
        """Handles a let expression by recurring on the expression and
        updating the cache
        """
        #pylint: disable=unused-argument
        self.consume_opening(tokens, "expression")
        newvals = {}
        current = "("
        self.consume_opening(tokens, "expression")
        while current != ")":
            if current != "(":
                raise PysmtSyntaxError("Expected '(' in let binding",
                                       tokens.pos_info)
            vname = self.parse_atom(tokens, "expression")
            expr = self.get_expression(tokens)
            newvals[vname] = expr
            self.cache.bind(vname, expr)
            self.consume_closing(tokens, "expression")
            current = tokens.consume()

        stack[-1].append(self._exit_let_expand)
        stack[-1].append(newvals.keys())

    def _exit_let_expand(self, varlist, bdy):
        """ Cleans the execution environment when we exit the scope of a 'let' """
        for k in varlist:
            self.cache.unbind(k)
        return bdy

    def _enter_let(self, stack, tokens, key):
        """Handles a let expression by recurring on the expression and
        updating the cache
        """
        # pylint: disable=unused-argument
        self.consume_opening(tokens, "expression")
        newvals = {}
        current = "("
        self.consume_opening(tokens, "expression")
        while current != ")":
            if current != "(":
                raise PysmtSyntaxError("Expected '(' in let binding", tokens.pos_info)
            vname = self.parse_atom(tokens, "expression", include_pipes=True)
            expr = self.get_expression(tokens)
            # variable has same type as its definition
            var = self._get_quantified_var(vname, expr.get_type(), prefix="lv")
            newvals[(vname, var)] = expr
            self.cache.bind(vname, var)
            self.consume_closing(tokens, "expression")
            current = tokens.consume()

        stack[-1].append(self._exit_let)
        # variables defined by let
        stack[-1].append(list(newvals.keys()))
        # corresponding expressions (definitions)
        stack[-1].append(list(newvals.values()))

    def _operator_adapter(self, operator):
        """Handles generic operator"""

        def res(stack, tokens, key):
            # pylint: disable=unused-argument
            stack[-1].append(operator)

        return res

    def _enter_quantifier(self, stack, tokens, key):
        """Handles quantifiers by defining the bound variable in the cache
        before parsing the matrix
        """
        mgr = self.env.formula_manager
        vrs = []
        self.consume_opening(tokens, "expression")
        current = "("
        self.consume_opening(tokens, "expression")
        while current != ")":
            if current != "(":
                raise PysmtSyntaxError("Expected '(' in let binding", tokens.pos_info)
            vname = self.parse_atom(tokens, "expression", include_pipes=True)
            typename = self.parse_type(tokens, "expression")

            var = self._get_quantified_var(vname, typename)
            self.cache.bind(vname, var)
            vrs.append((vname, var))

            self.consume_closing(tokens, "expression")
            current = tokens.consume()

        quant = None
        if key == "forall":
            quant = mgr.ForAll
        else:
            quant = mgr.Exists

        stack[-1].append(self._exit_quantifier)
        stack[-1].append(quant)
        stack[-1].append(vrs)

    def _enter_annotation(self, stack, tokens, key):
        """Deals with annotations"""
        # pylint: disable=unused-argument

        term = self.get_expression(tokens)
        annotations = ImmutableAnnotations()

        tk = tokens.consume()
        while tk != ")":
            if not tk.startswith(":"):
                raise PysmtSyntaxError(
                    "Annotations keyword should start with"
                    " colon! Offending token: '%s'" % tk,
                    tokens.pos_info,
                )
            keyword = tk[1:]
            tk = tokens.consume(include_pipes=True)
            value = None
            if tk == "(":
                counter = 1
                buff = [tk]
                while counter != 0:
                    tk = tokens.raw_read()
                    if tk == "(":
                        counter += 1
                    elif tk == ")":
                        counter -= 1
                    buff.append(tk)
                value = "".join(buff)
            else:
                value = tk 

            if value[0] == "(":
                # try to interpret value as an expression
                res = None
                try:
                    tmp_tokenizer = Tokenizer(StringIO(value))
                    res = self.get_expression(tmp_tokenizer)
                    value = res
                except:
                    res = None

                if res is None:
                    # try to interpret value as a list of expressions
                    if keyword in ["pattern", "no-pattern"]:
                        # the annotation should be a list of lists of expressions
                        tmp_tokenizer = Tokenizer(StringIO(value))
                        tk = tmp_tokenizer.consume()

                        assert tk == "("
                        # inside a list of s-expressions
                        res = []
                        while True:
                            try:
                                current = self.get_expression(tmp_tokenizer)
                                res.append(current)
                            except PysmtSyntaxError as e:
                                break

                        value = tuple(res)
            annotations = annotations.add(keyword, value)
            tk = tokens.consume()

        if len(annotations) > 0:
            term = self.env.formula_manager.Annotation(term, annotations)

        assert len(stack[-1]) == 0
        # re-add the ")" to the tokenizer because we consumed it, but
        # get_expression needs it
        tokens.add_extra_token(")")
        stack[-1].append(lambda: term)

    def get_expression(self, tokens):
        """
        Returns the pysmt representation of the given parsed expression
        """
        mgr = self.env.formula_manager
        stack = []

        try:
            while True:
                tk = tokens.consume_maybe()

                if tk == "(":
                    while tk == "(":
                        stack.append([])
                        tk = tokens.consume()

                    if tk in self.interpreted:
                        fun = self.interpreted[tk]
                        fun(stack, tokens, tk)
                    else:
                        stack[-1].append(self.atom(tk, tokens, mgr))

                elif tk == ")":
                    try:
                        lst = stack.pop()
                        fun = lst.pop(0)
                    except IndexError:
                        raise PysmtSyntaxError("Unexpected ')'", tokens.pos_info)

                    try:
                        res = fun(*lst)
                    except TypeError as err:
                        if not callable(fun):
                            raise NotImplementedError("Unknown function '%s'" % fun)
                        raise err

                    if len(stack) > 0:
                        stack[-1].append(res)
                    else:
                        return res

                else:
                    try:
                        stack[-1].append(self.atom(tk, tokens, mgr))
                    except IndexError:
                        return self.atom(tk, tokens, mgr)
        except StopIteration:
            # No more data when trying to consume tokens
            return

    def get_script(self, script):
        """
        Takes a file object and returns a SmtLibScript object representing
        the file
        """
        self._reset()  # prepare the parser
        res = SmtLibScript()
        for cmd in self.get_command_generator(script):
            res.add_command(cmd)
        return res

    def get_command_generator(self, script):
        """Returns a python generator of SmtLibCommand's given a file object
        to read from

        This function can be used interactively, and blocks until a
        whole command is read from the script.

        """
        tokens = Tokenizer(script, interactive=self.interactive)
        for cmd in self.get_command(tokens):
            yield cmd
        return

    def parse_model(self, script):
        """This function pasres the result of a `(get-model)` command and
        returns a model as a dictionary from non-function symbols to
        constant values and an interpretation for uninterpreted
        functions as a map from the function symbol to a
        FunctionInterpretation object.

        Example:
        ```
        model_source ="(model
          (define-fun b () Int 5)
          (define-fun a () Real 2)
          (define-fun f ((x0 Int)) Real (ite (> x0 5) 1 0.5))
        )"
        model_buf = StringIO(model_source)
        parser = SmtLibParser()
        model, interpretations = parser.parse_model(model_buf)
        ```
        gives:

        `model = {Symbol('a', INT): Int(5), Symbol('b', Real): Real(2)}`
        `interpretations = {Symbol('f', FunctionType(REAL, [INT])): fi}`

        where `fi = FunctionInterpretation([Symbol('x0', Int)], ITE(GT(Symbol('x0', Int), Int(5)), Real(1), Real(0.5)))`
        """
        mgr = self.env.formula_manager
        self.cache.update(self.env.type_manager._custom_types_decl)
        tokens = Tokenizer(script, interactive=self.interactive)
        current = tokens.consume()
        if current != "(":
            raise PysmtSyntaxError("'(' expected", tokens.pos_info)
        current = tokens.consume()

        # Backwards compatibility: skip optional model keyword
        if current == "model":
            current = tokens.consume()

        cmd_gen = self.get_command(tokens)
        model, interpretation = {}, {}
        while current != ")":
            if current != "(":
                raise PysmtSyntaxError("'(' expected", tokens.pos_info)
            tokens.add_extra_token(current)
            cmd = next(cmd_gen)
            if cmd.name != "define-fun":
                raise PysmtSyntaxError("Unsupported model command: %s" % cmd.name)
            vname, formal, rtype, ebody = cmd.args
            if len(formal) == 0:  # Constant assignment
                model[mgr.Symbol(vname, rtype)] = ebody
            else:  # A function interpretation
                ebody_free_vars = self.env.fvo.get_free_variables(ebody)
                for v in ebody_free_vars:
                    if not v.symbol_name().startswith("@") and v not in cmd.args[1]:
                        raise PysmtSyntaxError(
                            "Found a non-solver-defined free"
                            " variable in the definion of "
                            "function %s: %s" % (cmd.args[0], cmd.args[3])
                        )
                tmgr = self.env.type_manager
                ftype = tmgr.FunctionType(rtype, [x.symbol_type() for x in formal])
                interpretation[mgr.Symbol(vname, ftype)] = FunctionInterpretation(
                    formal, ebody, allow_free_vars=True
                )
            current = tokens.consume()
        return model, interpretation

    def get_script_fname(self, script_fname):
        """Given a filename and a Solver, executes the solver on the file."""
        with open_(script_fname) as script:
            return self.get_script(script)

    def parse_atoms(self, tokens, command, min_size, max_size=None):
        """
        Parses a sequence of N atoms (min_size <= N <= max_size) consuming
        the tokens
        """
        if max_size is None:
            max_size = min_size

        res = []
        current = None
        for _ in range(min_size):
            current = tokens.consume(
                "Unexpected end of stream in %s " "command." % command
            )
            if current == ")":
                raise PysmtSyntaxError(
                    "Expected at least %d arguments in "
                    "%s command." % (min_size, command),
                    tokens.pos_info,
                )
            if current == "(":
                raise PysmtSyntaxError(
                    "Unexpected token '(' in %s " "command." % command, tokens.pos_info
                )
            res.append(current)
        for _ in range(min_size, max_size + 1):
            current = tokens.consume(
                "Unexpected end of stream in %s " "command." % command
            )
            if current == ")":
                return res
            if current == "(":
                raise PysmtSyntaxError(
                    "Unexpected token '(' in %s " "command." % command, tokens.pos_info
                )
            res.append(current)
        raise PysmtSyntaxError(
            "Unexpected token '%s' in %s command. Expected "
            "at most %d arguments." % (current, command, max_size),
            tokens.pos_info,
        )

    def parse_type(self, tokens, command, type_params=None, additional_token=None):
        """Parses a single type name from the tokens"""
        if additional_token is not None:
            var = additional_token
        else:
            var = tokens.consume("Unexpected end of stream in %s command." % command)
        res = None
        if type_params and var in type_params:
            return (var,)  # This is a type parameter, it is handled recursively
        elif var == "(":
            op = tokens.consume("Unexpected end of stream in %s command." % command)
            if op == "Array":
                idxtype = self.parse_type(tokens, command, type_params=type_params)
                elemtype = self.parse_type(tokens, command, type_params=type_params)
                self.consume_closing(tokens, command)

                if isinstance(idxtype, tuple) or isinstance(elemtype, tuple):
                    # at least one of idxtype or elemtype are parametric
                    def definition(*args):
                        idxtype_concrete = (
                            args[type_params.index(idxtype[0])]
                            if isinstance(idxtype, tuple)
                            else idxtype
                        )
                        elemtype_concrete = (
                            args[type_params.index(elemtype[0])]
                            if isinstance(elemtype, tuple)
                            else elemtype
                        )
                        return self.env.type_manager.ArrayType(
                            idxtype_concrete, elemtype_concrete
                        )

                    res = PartialType(
                        "tmp", definition, "Array", [idxtype, elemtype], type_params
                    )
                else:
                    res = self.env.type_manager.ArrayType(idxtype, elemtype)

            elif op == "_":
                ts = tokens.consume("Unexpected end of stream in %s command." % command)
                if ts != "BitVec":
                    raise PysmtSyntaxError(
                        "Unexpected token '%s' in %s command." % (ts, command),
                        tokens.pos_info,
                    )

                size = 0
                dim = tokens.consume()
                try:
                    size = int(dim)
                except ValueError:
                    raise PysmtSyntaxError(
                        "Unexpected token '%s' in %s command." % (dim, command),
                        tokens.pos_info,
                    )

                self.consume_closing(tokens, command)
                res = self.env.type_manager.BVType(size)

            else:
                try:
                    # It must be a custom-defined type
                    base_type = self.cache.get(op)
                    if base_type is None or not (
                        isinstance(base_type, _TypeDecl)
                        or isinstance(base_type, PartialType)
                    ):
                        raise PysmtSyntaxError(
                            "Unexpected token '%s' in %s command." % (op, command),
                            tokens.pos_info,
                        )

                    pparams = []
                    has_free_params = False
                    for _ in range(base_type.arity):
                        ty = self.parse_type(tokens, command, type_params=type_params)
                        pparams.append(ty)
                        if isinstance(ty, tuple) or isinstance(ty, PartialType):
                            has_free_params = True
                    if has_free_params:

                        def definition(*args):
                            params = []
                            for x in pparams:
                                if isinstance(x, tuple):
                                    params.append(args[type_params.index(x[0])])
                                else:
                                    params.append(
                                        self.env.type_manager.get_type_instance(
                                            x, *args
                                        )
                                    )
                            return self.env.type_manager.get_type_instance(
                                base_type, *params
                            )

                        res = PartialType(
                            "tmp", definition, base_type.name, pparams, type_params
                        )
                    else:
                        res = self.env.type_manager.get_type_instance(
                            base_type, *pparams
                        )
                    self.consume_closing(tokens, command)

                except Exception as e:
                    # Interpret as parametric type, e.g., (Int Int) or (RegEx String) are valid in smtlib
                    # tokens.add_extra_token(op) # put op back
                    base_type = self.parse_type(tokens, command, additional_token=op)
                    parameters = []
                    next_token = tokens.consume()
                    while next_token != ")":
                        # tokens.add_extra_token(next_token)
                        parameters.append(
                            self.parse_type(
                                tokens, command, additional_token=next_token
                            )
                        )
                        next_token = tokens.consume()

                    if parameters:
                        res = self.env.type_manager.ParameterizedType(
                            base_type, parameters
                        )
                    else:
                        res = base_type

        elif var == "Bool":
            res = self.env.type_manager.BOOL()
        elif var == "Int":
            res = self.env.type_manager.INT()
        elif var == "Real":
            res = self.env.type_manager.REAL()
        elif var == "String":
            res = self.env.type_manager.STRING()
        elif (
            var == "RegLan" or var == "RegEx"
        ):  # RegEx added for back compatibility with some solvers
            res = self.env.type_manager.REGEX()
        elif var == "RoundingMode":
            res = self.env.type_manager.ROUNDING_MODE()
        else:
            res = self.cache.get(var)
            if res is None:
                raise PysmtSyntaxError(
                    "Unexpected token '%s' in %s command." % (var, command),
                    tokens.pos_info,
                )

        if isinstance(res, _TypeDecl):
            return self.env.type_manager.get_type_instance(res)
        else:
            return res

    def parse_atom(self, tokens, command, include_pipes=False):
        """Parses a single name from the tokens"""
        var = tokens.consume(
            "Unexpected end of stream in %s command." % command,
            include_pipes=include_pipes,
        )
        if var == "(" or var == ")":
            raise PysmtSyntaxError(
                "Unexpected token '%s' in %s command." % (var, command), tokens.pos_info
            )
        return var

    def parse_params(self, tokens, command):
        """Parses a list of types from the tokens"""
        self.consume_opening(tokens, command)
        current = tokens.consume("Unexpected end of stream in %s command." % command)
        res = []
        while current != ")":
            res.append(self.parse_type(tokens, command, additional_token=current))
            current = tokens.consume(
                "Unexpected end of stream in %s command." % command
            )
        return res

    def parse_named_params(self, tokens, command):
        """Parses a list of names and type from the tokens"""
        self.consume_opening(tokens, command)
        current = tokens.consume("Unexpected end of stream in %s command." % command)
        res = []
        while current != ")":
            vname = self.parse_atom(tokens, command)
            typename = self.parse_type(tokens, command)
            res.append((vname, typename))
            self.consume_closing(tokens, command)
            current = tokens.consume(
                "Unexpected end of stream in %s command." % command
            )
        return res

    def parse_expr_list(self, tokens, command):
        """Parses a list of expressions form the tokens"""
        self.consume_opening(tokens, command)
        res = []
        while True:
            try:
                current = self.get_expression(tokens)
                res.append(current)
            except PysmtSyntaxError:
                return res

    def consume_opening(self, tokens, command):
        """Consumes a single '('"""
        try:
            p = tokens.consume_maybe()
        except StopIteration:
            raise  # Re-raise execption for higher-level management, see get_command()
        if p != "(":
            raise PysmtSyntaxError(
                "Unexpected token '%s' in %s command. " "Expected '('" % (p, command),
                tokens.pos_info,
            )

    def consume_closing(self, tokens, command):
        """Consumes a single ')'"""
        p = tokens.consume("Unexpected end of stream. Expected ')'")
        if p != ")":
            raise PysmtSyntaxError(
                "Unexpected token '%s' in %s command. " "Expected ')'" % (p, command),
                tokens.pos_info,
            )

    def _function_call_helper(self, v, *args):
        """Helper function for dealing with function calls"""
        return self.env.formula_manager.Function(v, args)

    def get_assignment_list(self, script):
        """
        Parse an assignment list produced by get-model and get-value
        commands in SmtLib
        """
        symbols = self.env.formula_manager.symbols
        self.cache.update(symbols)
        tokens = Tokenizer(script, interactive=self.interactive)
        res = []
        self.consume_opening(tokens, "<main>")
        current = tokens.consume()
        while current != ")":
            if current != "(":
                raise PysmtSyntaxError("'(' expected", tokens.pos_info)
            vname = self.get_expression(tokens)
            expr = self.get_expression(tokens)
            self.consume_closing(tokens, current)
            res.append((vname, expr))
            current = tokens.consume()
        self.cache.unbind_all(symbols)
        return res

    def get_command(self, tokens):
        """Builds an SmtLibCommand instance out of a parsed term."""
        while True:
            try:
                self.consume_opening(tokens, "<main>")
            except StopIteration:
                # No openings
                return
            current = tokens.consume()
            if current in self.commands:
                fun = self.commands[current]
                yield fun(current, tokens)
            else:
                raise UnknownSmtLibCommandError(current)

    def _cmd_not_implemented(self, current, tokens):
        raise NotImplementedError("'%s' has not been implemented yet" % current)

    def _cmd_set_info(self, current, tokens):
        """(set-info <attribute>)"""
        elements = self.parse_atoms(tokens, current, 2)
        return SmtLibCommand(current, elements)

    def _cmd_set_option(self, current, tokens):
        """(set-option <option>)"""
        elements = self.parse_atoms(tokens, current, 2)
        return SmtLibCommand(current, elements)

    def _cmd_assert(self, current, tokens):
        """(assert <term>)"""
        expr = self.get_expression(tokens)
        self.consume_closing(tokens, current)
        return SmtLibCommand(current, [expr])

    def _cmd_check_sat(self, current, tokens):
        """(check-sat)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_push(self, current, tokens):
        """(push <numeral>)"""
        elements = self.parse_atoms(tokens, current, 0, 1)
        levels = 1
        if len(elements) > 0:
            levels = int(elements[0])
        return SmtLibCommand(current, [levels])

    def _cmd_pop(self, current, tokens):
        """(pop <numeral>)"""
        elements = self.parse_atoms(tokens, current, 0, 1)
        levels = 1
        if len(elements) > 0:
            levels = int(elements[0])
        return SmtLibCommand(current, [levels])

    def _cmd_exit(self, current, tokens):
        """(exit)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_set_logic(self, current, tokens):
        """(set-logic <symbol>)"""
        elements = self.parse_atoms(tokens, current, 1)
        name = elements[0]
        try:
            logic = get_logic_by_name(name)

            # HACK: deal with undefined logics as strings
            if isinstance(logic, str):
                self.logic = None
            else:
                self.logic = logic
            return SmtLibCommand(current, [logic])
        except UndefinedLogicError:
            warn("Unknown logic '" + name + "'. Ignoring set-logic command.")
            return SmtLibCommand(current, [None])

    def _cmd_declare_const(self, current, tokens):
        """(declare-const <symbol> <sort>)"""
        var = self.parse_atom(tokens, current, include_pipes=True)
        typename = self.parse_type(tokens, current)
        self.consume_closing(tokens, current)
        v = self._get_var(var, typename)
        self.cache.bind(var, v)
        return SmtLibCommand(current, [v])

    def _cmd_get_value(self, current, tokens):
        """(get-value (<term>+)"""
        params = self.parse_expr_list(tokens, current)
        self.consume_closing(tokens, current)
        return SmtLibCommand(current, params)

    def parse_selectors(self, tokens, command):
        current = tokens.consume("Unexpected end of stream in %s command." % command)
        if current == ")":
            return []

        selectors = []
        while current != ")":
            sel = self.parse_atom(tokens, command)
            ty = self.parse_type(tokens, command)
            self.consume_closing(tokens, command)
            selectors.append((sel, ty))
            current = tokens.consume(
                "Unexpected end of stream in %s command." % command
            )
        return selectors

    def parse_constructors(self, tokens, command):
        self.consume_opening(tokens, command)
        current = tokens.consume("Unexpected end of stream in %s command." % command)
        constructors = []
        while current != ")":
            assert current == "(", "Expected ( got %s" % current
            constructor = self.parse_atom(tokens, command)
            selectors = self.parse_selectors(tokens, command)
            constructors.append((constructor, selectors))
            current = tokens.consume(
                "Unexpected end of stream in %s command." % command
            )
        return constructors

    def declare_constructors_selectors(self, adt):
        # this is perhaps a hack: constructors and selectors are defined as functions of appropriate type
        assert isinstance(adt, ADT)
        for c, ss in adt.cs:
            param_types = [s[1] for s in ss]
            ret_type = adt
            ftype = self.env.type_manager.FunctionType(
                return_type=ret_type, param_types=param_types
            )

            # declare constructor as a function from params to ADT type
            v = self._get_var(c, ftype)
            adt.aux_functions += [v]

            if v.symbol_type().is_function_type():
                self.cache.bind(c, functools.partial(self._function_call_helper, v))
            else:
                # nullary constructor (e.g., Nil)
                self.cache.bind(c, v)

            # declare selectors (destructors) as functions from ADT to params
            for (s, ty) in ss:
                ftype = self.env.type_manager.FunctionType(
                    return_type=ty, param_types=[adt]
                )
                v = self._get_var(s, ftype)
                adt.aux_functions += [v]
                assert v.symbol_type().is_function_type(), "Expected a function type"
                self.cache.bind(s, functools.partial(self._function_call_helper, v))

    def _cmd_declare_datatype(self, current, tokens):
        """(declare-datatype ...)"""
        var = self.parse_atom(tokens, current)
        # create the type right away in case of recursion
        type_ = ADT(var, None)
        self.cache.bind(var, type_)

        constructors = self.parse_constructors(tokens, current)
        self.consume_closing(tokens, current)

        type_.cs = constructors
        # declare constructors and selectors
        self.declare_constructors_selectors(type_)

        return SmtLibCommand(current, [type_])

    def parse_adt_names_arities(self, tokens, command):
        self.consume_opening(tokens, command)
        current = tokens.consume("Unexpected end of stream in %s command." % command)
        adts = []
        while current != ")":
            assert current == "(", "Expected ( got %s" % current
            name, arity = self.parse_atoms(tokens, command, 2)
            assert arity == "0", "Currently we do not support parametric ADTs"
            adts.append(name)
            current = tokens.consume(
                "Unexpected end of stream in %s command." % command
            )
        return adts

    def _cmd_declare_multiple_datatypes(self, current, tokens):
        """(declare-datatypes ...) NOTE: the dataype*S* not datatype"""
        command = current
        # TODO: test if arity larger than 0 is supported
        adt_names = self.parse_adt_names_arities(tokens, current)

        # declare ADTs right away in case of recursion
        adts = []
        for name in adt_names:
            adt = ADT(name, None)
            adts.append(adt)
            self.cache.bind(name, adt)

        current = tokens.consume()
        constructor_list = []
        while True:
            constructors = self.parse_constructors(tokens, "declare-datatype*S*")
            constructor_list.append(constructors)
            current = tokens.consume()
            if current == ")":
                break
            tokens.add_extra_token(current)
        self.consume_closing(tokens, current)

        assert len(adts) == len(
            constructor_list
        ), "Mismatch between number of declared ADTs and definitions"

        # update ADTs with constructors
        for name, adt, constructors in zip(adt_names, adts, constructor_list):
            adt.cs = constructors

            # declare constructors and selectors
            self.declare_constructors_selectors(adt)

        return SmtLibCommand(command, adts)

    def _cmd_declare_fun(self, current, tokens):
        """(declare-fun <symbol> (<sort>*) <sort>)"""
        var = self.parse_atom(tokens, current)
        params = self.parse_params(tokens, current)
        typename = self.parse_type(tokens, current)
        self.consume_closing(tokens, current)

        if params:
            typename = self.env.type_manager.FunctionType(typename, params)

        v = self._get_var(var, typename)
        if v.symbol_type().is_function_type():
            self.cache.bind(var, functools.partial(self._function_call_helper, v))
        else:
            self.cache.bind(var, v)
        return SmtLibCommand(current, [v])

    def _cmd_define_fun(self, current, tokens):
        """(define-fun <fun_def>)"""
        formal = []
        var = self.parse_atom(tokens, current)
        namedparams = self.parse_named_params(tokens, current)
        # types of params / like in declare-fun
        params = [t for (x, t) in namedparams]
        rtype = self.parse_type(tokens, current)
        bindings = []
        for (x, t) in namedparams:
            v = self.env.formula_manager.FreshSymbol(
                typename=t, template="__" + x + "%d"
            )
            self.cache.bind(x, v)
            formal.append(v)  # remember the variable
            bindings.append(x)  # remember the name
        # Parse expression using also parameters
        ebody = self.get_expression(tokens)
        ebody_type = self.env.stc.get_type(ebody)
        ebody_vars = self.env.fvo.get_free_variables(ebody)
        # Promote constant integer expression to real
        if ebody_type.is_int_type() and rtype.is_real_type() and len(ebody_vars) == 0:
            ebody = self.env.formula_manager.ToReal(ebody)
            ebody_type = rtype
        # Check that ebody has the right type
        if ebody_type != rtype:
            raise PysmtSyntaxError(
                "Typyng error in define-fun command. "
                "The expected type is %s, but the detected "
                "expression type is %s" % (rtype, ebody_type)
            )

        # Discard parameters
        for x in bindings:
            self.cache.unbind(x)
        # Finish Parsing
        self.consume_closing(tokens, current)

        if params:
            typename = self.env.type_manager.FunctionType(rtype, params)
        else:
            typename = rtype

        v = self._get_var(var, typename)
        if v.symbol_type().is_function_type():
            self.cache.bind(var, functools.partial(self._function_call_helper, v))
        else:
            self.cache.bind(var, v)

        self.cache.define(var, formal, ebody)
        return SmtLibCommand(current, [var, formal, rtype, ebody])

    def _cmd_declare_sort(self, current, tokens):
        """(declare-sort <symbol> <numeral>)"""
        (typename, arity) = self.parse_atoms(tokens, current, 2)
        try:
            type_ = self.env.type_manager.Type(typename, int(arity))
        except ValueError:
            raise PysmtSyntaxError(
                "Expected an integer as arity of type %s." % typename, tokens.pos_info
            )
        self.cache.bind(typename, type_)
        return SmtLibCommand(current, [type_])

    def _cmd_define_sort(self, current, tokens):
        """(define-sort <name> <args> <fun_def>)"""
        name = self.parse_atom(tokens, current)
        self.consume_opening(tokens, current)

        params = []
        cur = tokens.consume()
        while cur != ")":
            params.append(cur)
            cur = tokens.consume()

        rtype = self.parse_type(tokens, current, type_params=params)
        if isinstance(rtype, PartialType):
            rtype.name = name
        elif isinstance(rtype, tuple):

            def definition(*args):
                return args[params.index(rtype[0])]

            rtype = PartialType(name, definition)
        self.consume_closing(tokens, current)
        self.cache.define(name, [], rtype)
        return SmtLibCommand(current, [name, params, rtype])

    def _cmd_get_assertions(self, current, tokens):
        """(get-assertions)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_get_info(self, current, tokens):
        """(get-info <info_flag>)"""
        keyword = self.parse_atoms(tokens, current, 1)
        return SmtLibCommand(current, keyword)

    def _cmd_get_model(self, current, tokens):
        """(get-model)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_get_option(self, current, tokens):
        """(get-option <keyword>)"""
        keyword = self.parse_atoms(tokens, current, 1)
        return SmtLibCommand(current, keyword)

    def _cmd_get_proof(self, current, tokens):
        """(get-proof)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_get_unsat_core(self, current, tokens):
        """(get-unsat-core)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_check_sat_assuming(self, current, tokens):
        """(check-sat-assuming (<prop_literal>*) )"""
        params = self.parse_expr_list(tokens, current)
        self.consume_closing(tokens, current)
        return SmtLibCommand(current, params)

    def _cmd_define_fun_rec(self, current, tokens):
        """(define-fun-rec <fun_def>)"""
        return self._cmd_not_implemented(current, tokens)

    def _cmd_define_funs_rec(self, current, tokens):
        """(define-funs-rec (<fun_dec>^{n+1}) (<term>^{n+1>))"""
        return self._cmd_not_implemented(current, tokens)

    def _cmd_echo(self, current, tokens):
        """(echo <string>)"""
        elements = self.parse_atoms(tokens, current, 1)
        return SmtLibCommand(current, elements)

    def _cmd_get_assignment(self, current, tokens):
        """(get-assignment)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_get_unsat_assumptions(self, current, tokens):
        """(get-unsat-assumptions)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])

    def _cmd_reset(self, current, tokens):
        """(reset)"""
        self.parse_atoms(tokens, current, 0)
        # first reset the environment
        self.env = reset_env()
        # then reset the parser state (which will use the new env)
        self._reset()
        return SmtLibCommand(current, [])

    def _cmd_reset_assertions(self, current, tokens):
        """(reset-assertions)"""
        self.parse_atoms(tokens, current, 0)
        return SmtLibCommand(current, [])


# EOC SmtLibParser


class SmtLib20Parser(SmtLibParser):
    """Parser for SMT-LIB 2.0."""

    def __init__(self, environment=None, interactive=False):
        SmtLibParser.__init__(self, environment, interactive)

        # Remove commands that were introduced in SMT-LIB 2.5
        del self.commands["check-sat-assuming"]
        del self.commands["declare-const"]
        del self.commands["define-fun-rec"]
        del self.commands["define-funs-rec"]
        del self.commands["echo"]
        del self.commands["get-assignment"]
        del self.commands["get-unsat-assumptions"]
        del self.commands["reset"]
        del self.commands["reset-assertions"]


# EOC SmtLib20Parser


class SmtLibZ3Parser(SmtLibParser):
    """
    Parses extended Z3 SmtLib Syntax
    """

    def __init__(self, environment=None, interactive=False):
        SmtLibParser.__init__(self, environment, interactive)

        # Z3 prints Pow as "^"
        self.interpreted["^"] = self.interpreted["pow"]
        self.interpreted["ext_rotate_left"] = self._operator_adapter(
            self._ext_rotate_left
        )
        self.interpreted["ext_rotate_right"] = self._operator_adapter(
            self._ext_rotate_right
        )
        mgr = self.env.formula_manager
        self.interpreted["bv2int"] = self._operator_adapter(mgr.BVToNatural)

    def _ext_rotate_left(self, x, y):
        return self.env.formula_manager.BVRol(x, y.simplify().constant_value())

    def _ext_rotate_right(self, x, y):
        return self.env.formula_manager.BVRor(x, y.simplify().constant_value())


# EOC SmtLibZ3Parser
