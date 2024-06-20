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

from functools import reduce
import warnings
from collections import namedtuple
from io import StringIO
from pysmt.fnode import FNode

import pysmt.smtlib.commands as smtcmd
from pysmt.exceptions import (
    UnknownSmtLibCommandError,
    NoLogicAvailableError,
    UndefinedLogicError,
    PysmtValueError,
)
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.oracles import get_logic
from pysmt.logics import (
    get_closer_smtlib_logic,
    Logic,
    SMTLIB2_LOGICS,
    ALL as ALL_LOGICS,
)
from pysmt.environment import get_env
from pysmt.smtlib.utils import UnionFind


def check_sat_filter(log):
    """
    Returns the result of the check-sat command from a log.

    Raises errors in case a unique check-sat command cannot be located.
    """
    filtered = [(x, y) for x, y in log if x == smtcmd.CHECK_SAT]
    assert len(filtered) == 1
    return filtered[0][1]


class SmtLibCommand(namedtuple("SmtLibCommand", ["name", "args"])):
    def serialize(self, outstream=None, printer=None, daggify=True):
        """Serializes the SmtLibCommand into outstream using the given printer.

        Exactly one of outstream or printer must be specified. When
        specifying the printer, the associated outstream will be used.
        If printer is not specified, daggify controls the printer to
        be created. If true a daggified formula is produced, otherwise
        a tree printing is done.

        """

        if (outstream is None) and (printer is not None):
            outstream = printer.stream
        elif (outstream is not None) and (printer is None):
            if daggify:
                printer = SmtDagPrinter(outstream)
            else:
                printer = SmtPrinter(outstream)
        else:
            assert (outstream is not None and printer is not None) or (
                outstream is None and printer is None
            ), "Exactly one of outstream and printer must be set."

        if self.name == smtcmd.SET_OPTION:
            outstream.write("(%s %s %s)" % (self.name, self.args[0], self.args[1]))

        elif self.name == smtcmd.SET_INFO:
            outstream.write(
                "(%s %s %s)" % (self.name, self.args[0], quote(self.args[1]))
            )

        elif self.name == smtcmd.ASSERT:
            outstream.write("(%s " % self.name)
            printer.printer(self.args[0])
            outstream.write(")")

        elif self.name == smtcmd.GET_VALUE:
            outstream.write("(%s (" % self.name)
            for a in self.args:
                printer.printer(a)
                outstream.write(" ")
            outstream.write("))")

        elif self.name in [
            smtcmd.CHECK_SAT,
            smtcmd.EXIT,
            smtcmd.RESET,
            smtcmd.RESET_ASSERTIONS,
            smtcmd.GET_UNSAT_CORE,
            smtcmd.GET_ASSIGNMENT,
            smtcmd.GET_MODEL,
        ]:
            outstream.write("(%s)" % self.name)

        elif self.name == smtcmd.SET_LOGIC:
            outstream.write("(%s %s)" % (self.name, self.args[0]))

        elif self.name == smtcmd.DECLARE_FUN:
            symbol = self.args[0]
            type_str = symbol.symbol_type().as_smtlib()
            outstream.write(
                "(%s %s %s)" % (self.name, quote(symbol.symbol_name()), type_str)
            )

        elif self.name == smtcmd.DECLARE_CONST:
            symbol = self.args[0]
            type_str = symbol.symbol_type().as_smtlib(funstyle=False)
            outstream.write(
                "(%s %s %s)" % (self.name, quote(symbol.symbol_name()), type_str)
            )

        elif self.name == smtcmd.DEFINE_FUN:
            name = quote(self.args[0])
            params_list = self.args[1]
            params = " ".join(
                [
                    "(%s %s)" % (v, v.symbol_type().as_smtlib(funstyle=False))
                    for v in params_list
                ]
            )
            rtype = self.args[2]
            expr = self.args[3]
            outstream.write(
                "(%s %s (%s) %s "
                % (self.name, name, params, rtype.as_smtlib(funstyle=False))
            )
            printer.printer(expr)
            outstream.write(")")

        elif self.name in [smtcmd.PUSH, smtcmd.POP]:
            outstream.write("(%s %d)" % (self.name, self.args[0]))

        elif self.name == smtcmd.DEFINE_SORT:
            name = self.args[0]
            params_list = self.args[1]
            params = " ".join(
                x if isinstance(x, str) else x.as_smtlib(funstyle=False)
                for x in params_list
            )
            rtype = self.args[2]
            outstream.write(
                "(%s %s (%s) %s)"
                % (self.name, name, params, rtype.as_smtlib(funstyle=False))
            )

        elif self.name == smtcmd.DECLARE_SORT:
            type_decl = self.args[0]
            outstream.write("(%s %s %d)" % (self.name, type_decl.name, type_decl.arity))

        elif self.name == smtcmd.GET_INFO:
            args_str = " ".join(self.args)
            outstream.write("(%s %s)" % (self.name, args_str))

        elif self.name == smtcmd.DECLARE_DATATYPE:
            name = self.args[0].basename
            adt = self.args[0]
            outstream.write("(%s %s %s)" % (self.name, name, adt.smtlib_decl()))

        elif self.name == smtcmd.DECLARE_DATATYPES:
            names = ["(" + n.basename + " 0)" for n in self.args]
            names = "(" + " ".join(names) + ")"
            decls = [n.smtlib_decl() for n in self.args]
            decls = "(" + " ".join(decls) + ")"
            outstream.write("(%s %s %s)" % (self.name, names, decls))

        elif self.name in smtcmd.ALL_COMMANDS:
            raise NotImplementedError(
                "'%s' is a valid SMT-LIB command "
                "but it is currently not supported. "
                "Please open a bug-report." % self.name
            )
        else:
            raise UnknownSmtLibCommandError(self.name)

    def serialize_to_string(self, daggify=True):
        buf = StringIO()
        self.serialize(buf, daggify=daggify)
        return buf.getvalue()


class SmtLibScript(object):
    def __init__(self):
        self.commands = []

    def add(self, name, args):
        """Adds a new SmtLibCommand with the given name and arguments."""
        self.add_command(SmtLibCommand(name=name, args=args))

    def add_command(self, command):
        self.commands.append(command)

    def evaluate(self, solver):
        log = []
        for cmd in self.commands:
            r = evaluate_command(cmd, solver)
            log.append((cmd.name, r))
        return log

    def contains_command(self, command_name):
        return any(x.name == command_name for x in self.commands)

    def count_command_occurrences(self, command_name):
        return sum(1 for cmd in self.commands if cmd.name == command_name)

    def filter_by_command_name(self, command_name_set):
        return (cmd for cmd in self.commands if cmd.name in command_name_set)

    def get_strict_formula(self, mgr=None):
        if self.contains_command(smtcmd.PUSH) or self.contains_command(smtcmd.POP):
            raise PysmtValueError("Was not expecting push-pop commands")
        if self.count_command_occurrences(smtcmd.CHECK_SAT) != 1:
            raise PysmtValueError("Was expecting exactly one check-sat command")
        _And = mgr.And if mgr else get_env().formula_manager.And

        assertions = [
            cmd.args[0] for cmd in self.filter_by_command_name([smtcmd.ASSERT])
        ]
        return _And(assertions)

    def get_declared_symbols(self):
        return {
            cmd.args[0]
            for cmd in self.filter_by_command_name(
                [smtcmd.DECLARE_CONST, smtcmd.DECLARE_FUN, smtcmd.DEFINE_FUN, smtcmd.DEFINE_FUN_REC, smtcmd.DEFINE_FUNS_REC]
            )
        }

    def get_define_fun_parameter_symbols(self):
        res = set()
        for cmd in self.filter_by_command_name([smtcmd.DEFINE_FUN]):
            for s in cmd.args[1]:
                res.add(s)
        return res

    def get_last_formula(self, mgr=None):
        """Returns the last formula of the execution of the Script.

        This coincides with the conjunction of the assertions that are
        left on the assertion stack at the end of the SMTLibScript.
        """
        stack = []
        backtrack = []
        _And = mgr.And if mgr else get_env().formula_manager.And

        for cmd in self.commands:
            if cmd.name == smtcmd.ASSERT:
                stack.append(cmd.args[0])
            if cmd.name == smtcmd.RESET_ASSERTIONS:
                stack = []
                backtrack = []
            elif cmd.name == smtcmd.PUSH:
                for _ in range(cmd.args[0]):
                    backtrack.append(len(stack))
            elif cmd.name == smtcmd.POP:
                for _ in range(cmd.args[0]):
                    l = backtrack.pop()
                    stack = stack[:l]

        return _And(stack)

    def to_file(self, fname, daggify=True):
        with open(fname, "w") as outstream:
            self.serialize(outstream, daggify=daggify)

    def serialize(self, outstream, daggify=True):
        """Serializes the SmtLibScript expanding commands"""
        if daggify:
            printer = SmtDagPrinter(outstream)
        else:
            printer = SmtPrinter(outstream)

        for cmd in self.commands:
            cmd.serialize(printer=printer)
            outstream.write("\n")

    def __len__(self):
        return len(self.commands)

    def __iter__(self):
        return iter(self.commands)

    def __str__(self):
        return "\n".join((str(cmd) for cmd in self.commands))


def smtlibscript_from_formula(formula, logic=None, environment=get_env()):
    script = SmtLibScript()

    try:
        if logic is None:
            # Get the simplest SmtLib logic that contains the formula
            f_logic = get_logic(formula)

            smt_logic = ALL_LOGICS
            try:
                smt_logic = get_closer_smtlib_logic(f_logic)
            except NoLogicAvailableError:
                warnings.warn(
                    "The logic %s is not reducible to any SMTLib2 "
                    "standard logic. Proceeding with non-standard "
                    "logic '%s'" % (f_logic, f_logic),
                    stacklevel=3,
                )
                smt_logic = f_logic
        elif not (isinstance(logic, Logic) or isinstance(logic, str)):
            raise UndefinedLogicError(str(logic))
        else:
            if logic not in SMTLIB2_LOGICS:
                warnings.warn(
                    "The logic %s is not reducible to any SMTLib2 "
                    "standard logic. Proceeding with non-standard "
                    "logic '%s'" % (logic, logic),
                    stacklevel=3,
                )
            smt_logic = logic
    except:
        # Could not figure out automatically which logic to use so falling back to ALL
        smt_logic = ALL_LOGICS
        pass

    script.add(name=smtcmd.SET_LOGIC, args=[smt_logic])

    # Declare all types
    types = environment.typeso.get_types(formula, custom_only=True)
    non_adt_types = set([t for t in types if not t.is_adt_type()])
    for type_ in non_adt_types:
        script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])

    adt_types = [t for t in types if t.is_adt_type()]

    # find indirectly recursive ADTs, which should be declared in a single statement.
    # We partition the declaration into dependent components and serialize each
    # component only once
    missing_non_adt_declarations = set()
    uf = UnionFind()
    for adt in adt_types:
        uf.add(adt)
        types_it_depends_on = set(adt.get_types_it_depends_on(transitively=True))
        for t in types_it_depends_on:
            if t.is_adt_type():
                uf.union(adt, t)
            else:
                if t.is_custom_type() and t not in non_adt_types:
                    missing_non_adt_declarations.add(t)

    for type_ in missing_non_adt_declarations:
        script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])

    for component in uf.get_components():
        # in case an adt depends on a non-adt sort that has never been used alone in the file,
        # this sort may not have been declared. Sorting it here
        


        smt_command = (
            smtcmd.DECLARE_DATATYPE if len(component) == 1 else smtcmd.DECLARE_DATATYPES
        )
        script.add(name=smt_command, args=list(component))

    # collect list of ADT constructor functions to avoid redeclaring them
    adt_constructors_aux_functions = reduce(
        lambda x, y: x + y, [adt.aux_functions for adt in adt_types], []
    )

    deps = formula.get_free_variables()
    # Declare all variables
    for symbol in deps:
        assert symbol.is_symbol()
        # if it is an auxiliary function introduced when parsing an ADT declaration, do not serialize it
        if symbol in adt_constructors_aux_functions:
            continue

        script.add(name=smtcmd.DECLARE_FUN, args=[symbol])

    # Assert formula
    script.add_command(SmtLibCommand(name=smtcmd.ASSERT, args=[formula]))
    # check-sat
    script.add_command(SmtLibCommand(name=smtcmd.CHECK_SAT, args=[]))
    return script


def evaluate_command(cmd, solver):
    if cmd.name == smtcmd.SET_INFO:
        return solver.set_info(cmd.args[0], cmd.args[1])

    if cmd.name == smtcmd.SET_OPTION:
        opt = cmd.args[0]
        if opt[0] == ":":
            opt = opt[1:]
        return solver.set_option(opt, cmd.args[1])

    elif cmd.name == smtcmd.ASSERT:
        return solver.assert_(cmd.args[0])

    elif cmd.name == smtcmd.CHECK_SAT:
        return solver.check_sat()

    elif cmd.name == smtcmd.RESET_ASSERTIONS:
        return solver.reset_assertions()

    elif cmd.name == smtcmd.GET_VALUE:
        return solver.get_values(cmd.args)

    elif cmd.name == smtcmd.PUSH:
        return solver.push(cmd.args[0])

    elif cmd.name == smtcmd.POP:
        return solver.pop(cmd.args[0])

    elif cmd.name == smtcmd.EXIT:
        return solver.exit()

    elif cmd.name == smtcmd.SET_LOGIC:
        name = cmd.args[0]
        return solver.set_logic(name)

    elif cmd.name == smtcmd.DECLARE_FUN:
        return solver.declare_fun(cmd.args[0])

    elif cmd.name == smtcmd.DECLARE_CONST:
        return solver.declare_const(cmd.args[0])

    elif cmd.name == smtcmd.DEFINE_FUN:
        (var, formals, typename, body) = cmd.args
        return solver.define_fun(var, formals, typename, body)

    elif cmd.name == smtcmd.ECHO:
        return None

    elif cmd.name == smtcmd.CHECK_SAT_ASSUMING:
        return solver.check_sat(cmd.args)

    elif cmd.name == smtcmd.GET_UNSAT_CORE:
        return solver.get_unsat_core()

    elif cmd.name == smtcmd.GET_MODEL:
        return solver.get_model()

    elif cmd.name == smtcmd.DECLARE_SORT:
        name = cmd.args[0].name
        arity = cmd.args[0].arity
        return solver.declare_sort(name, arity)

    elif cmd.name in smtcmd.ALL_COMMANDS:
        raise NotImplementedError(
            "'%s' is a valid SMT-LIB command "
            "but it is currently not supported. "
            "Please open a bug-report." % cmd.name
        )
    else:
        raise UnknownSmtLibCommandError(cmd.name)
