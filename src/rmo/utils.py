import logging
from contextlib import contextmanager
from functools import reduce
from time import perf_counter
from typing import Callable, Dict, Iterable, List, Set

import pysmt.operators as op
import pysmt.smtlib.commands as smtcmd
from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.smtlib.script import SmtLibScript, smtlibscript_from_formula
from pysmt.typing import PySMTType, _TypeDecl
from pysmt.walkers import DagWalker, handles

logger = logging.getLogger(__name__)


def copy_script_replace_assertions(script: SmtLibScript, assertion_to_formula):
    collapsed_assertions = len(assertion_to_formula) == 1 and -1 in assertion_to_formula.keys()

    res = SmtLibScript()
    for i, cmd in enumerate(script.commands):
        if collapsed_assertions:
            if cmd.name != smtcmd.ASSERT:
                if cmd.name == smtcmd.CHECK_SAT:
                    res.add(smtcmd.ASSERT, [assertion_to_formula[-1]])
                res.add_command(cmd)
        else:
            if cmd.name == smtcmd.ASSERT:
                if assertion_to_formula[i] is not None:
                    res.add(smtcmd.ASSERT, [assertion_to_formula[i]])
            else:
                res.add_command(cmd)

    return res


def merge_obfuscated(
    script: SmtLibScript,
    assertion_to_formula,
    replaced_names_mapping: Dict[str, str],
    names_failed_to_obfuscate: Set[str] = set(),
):
    """Replace declarations and assertions in the original script with the obfuscated ones"""
    collapsed_assertions = len(assertion_to_formula) == 1 and -1 in assertion_to_formula.keys()

    env = Environment()

    and_of_all_assertions = env.formula_manager.And(
        env.formula_manager.normalize(f) for f in assertion_to_formula.values() if f is not None
    )

    # Construct obfuscated script containing alla and only the necessary, obfuscated
    # declarations and definitions
    # This may not work correctly if a function is redefined with different
    # sorts within different push/pop contexts.
    obfuscated_script_defs = smtlibscript_from_formula(
        and_of_all_assertions,
        smtlibscript_from_formula,
    )

    # Identify all adt types and their constructors to avoid redefining them as functions
    types = env.typeso.get_types(and_of_all_assertions, custom_only=True)
    adt_types = [t for t in types if t.is_adt_type()]
    all_adt_types = set(adt_types)
    for adt_t in adt_types:
        for dt in adt_t.get_types_it_depends_on(transitively=True):
            if dt.is_adt_type():
                all_adt_types.add(dt)
    constructor_and_selectors_names = set()
    for adt in all_adt_types:
        for cs in adt.cs:
            constructor_and_selectors_names.add(cs[0])  # constructor name
            for s in cs[1]:
                constructor_and_selectors_names.add(s[0])  # selector name

    def find_type_name(formula):
        # assumes that formula is a definition or a declaration
        if isinstance(formula, _TypeDecl):
            return formula.name
        if isinstance(formula, PySMTType):
            return formula.basename
        if isinstance(formula, str):
            return formula
        return formula.symbol_name()

    obfuscated_defs_by_name = {
        find_type_name(cmd.args[0]): cmd
        for cmd in obfuscated_script_defs.commands
        if cmd.name.startswith("define") or cmd.name.startswith("declare")
    }

    # declare-datatypes can declare multiple datatypes with a single command.
    # We keep the first one as representative in obfuscated_defs_by_name and
    # link the other datatype names to it in transitive_defs_by_name below
    transitive_defs_by_name = {
        find_type_name(a): find_type_name(cmd.args[0])
        for cmd in obfuscated_script_defs.commands
        for a in cmd.args
        if cmd.name == smtcmd.DECLARE_DATATYPES
    }

    def find_obfuscated(name):
        return replaced_names_mapping.get(name, None)

    res = SmtLibScript()

    for i, cmd in enumerate(script.commands):
        # Temporary patch to avoid redefining RoundingMode. It should be unnecessary after we integrate FP theory in PySMT
        if cmd.name == smtcmd.DECLARE_SORT and cmd.args[0].name == "RoundingMode":
            continue

        if cmd.name.startswith("define") or cmd.name.startswith("declare"):
            # short-circuit to skip redefining DT constructors
            if cmd.name == smtcmd.DECLARE_FUN:
                if cmd.args[0].symbol_name() in constructor_and_selectors_names:
                    continue

            original_name = find_type_name(cmd.args[0])
            obfuscated_name = find_obfuscated(original_name)

            if obfuscated_name is not None:
                if obfuscated_name in transitive_defs_by_name:
                    obfuscated_name = transitive_defs_by_name[obfuscated_name]
                res.add_command(obfuscated_defs_by_name[obfuscated_name])
            else:
                if original_name in names_failed_to_obfuscate:
                    # if the name could not be obfuscated, it will be included in cleartext.
                    # if instead the name does not appear among either the obfuscated nor the failed to obfuscate names,
                    # it relates to an element of the original file that is not used in the final obfuscated one and can
                    # be dropped (e.g., removed by minimization)
                    res.add_command(cmd)

        elif cmd.name == smtcmd.ASSERT:
            if not collapsed_assertions:
                if assertion_to_formula[i] is not None:
                    # None means the assertion has been eliminated from the problem by a minimization step
                    res.add(smtcmd.ASSERT, [assertion_to_formula[i]])

        elif cmd.name in [smtcmd.CHECK_SAT, smtcmd.CHECK_SAT_ASSUMING]:
            if collapsed_assertions:
                # if all the assertions have been collapsed into one, it should be asserted before the check command
                res.add(smtcmd.ASSERT, [assertion_to_formula[-1]])
            res.add_command(cmd)

        else:
            # filter out comments or other unnecessary info
            if cmd.name not in [smtcmd.SET_INFO, smtcmd.ECHO]:
                res.add_command(cmd)

    return res


class NodeCollectorWalker(DagWalker):
    def __init__(
        self,
        selector: Callable[[FNode, Iterable[FNode]], bool],
        skip_subtree: Callable[[FNode, Iterable[FNode]], bool] = lambda x, y: False,
        env=None,
        invalidate_memoization=True,
    ):
        super().__init__(env, invalidate_memoization)
        self._selector: Callable[[FNode, Iterable[FNode]], bool] = selector
        self._skip_subtree: Callable[[FNode, Iterable[FNode]], bool] = skip_subtree

    def walk(self, formula, **kwargs):
        res = super().walk(formula, **kwargs)
        return res

    @handles(op.ALL_TYPES)
    def walk_node(self, formula, args, **kwargs):
        res = set()
        if self._skip_subtree(formula, args):
            return res
        if self._selector(formula, args):
            res.add(formula)

        if args is not None:
            res = reduce(lambda s1, s2: s1 | s2, args, res)
        return res

    @handles(op.ANNOTATION)
    def walk_annotation(self, formula, args, **kwargs):
        res = self.walk_node(formula, args, **kwargs)

        # deep traversal of annotation
        annotations = formula.get_annotations()
        for k in annotations:
            values = annotations[k]
            for v in values:
                if isinstance(v, tuple):
                    # it is a list of s-expr (FNodes), which should each be traversed
                    res = reduce(
                        lambda s1, s2: s1 | s2,
                        [self.memoization[sexpr] for sexpr in v],
                        res,
                    )
                elif isinstance(v, FNode):
                    res = res | self.walk(v, **kwargs)

        return res

    @handles(op.LET)
    def walk_let(self, formula, args, **kwargs):
        res = self.walk_node(formula, args, **kwargs)
        res = reduce(
            lambda s1, s2: s1 | s2,
            [self.memoization[e] for v, e in formula.let_defs()],
            res,
        )
        return res


class TimeoutBudget:
    def __init__(self, initial_budget: float = float("inf")) -> None:
        self._budget: float = initial_budget

    def available(self) -> bool:
        return self._budget > 0

    def deduct(self, amount: float) -> None:
        assert amount >= 0
        self._budget -= amount


class MultipleTimeoutBudget(TimeoutBudget):
    """Keep tracks simulataneously of multiple budgets, decreasing all of them and becoming unavailable if at least one budget is <= 0"""

    def __init__(self, *budgets: Iterable[TimeoutBudget]) -> None:
        super().__init__(None)
        self._budgets: List[TimeoutBudget] = list(budgets)

    def available(self) -> bool:
        return all(b.available() for b in self._budgets)

    def deduct(self, amount: float) -> None:
        assert amount >= 0
        for b in self._budgets:
            b.deduct(amount)


InfiniteTimeoutBudget = TimeoutBudget(initial_budget=float("inf"))


@contextmanager
def track_timeout_budget(budget: TimeoutBudget) -> None:
    start_time = perf_counter()
    yield
    step_duration = perf_counter() - start_time
    budget.deduct(step_duration)


class HashDict:
    def __init__(self, *args, **kwargs) -> None:
        self._dict = dict(*args, **kwargs)
        self._hash = None

    def __getitem__(self, key):
        return self._dict[key]

    def __contains__(self, key):
        return key in self._dict

    def __iter__(self):
        return iter(self._dict)

    def __len__(self):
        return len(self._dict)

    def set_item(self, key, value):
        new_dict = dict(self._dict)
        new_dict[key] = value
        return HashDict(new_dict)

    def del_key(self, key):
        new_dict = dict(self._dict)
        new_dict.pop(key)
        return HashDict(new_dict)

    def get(self, key, default=None):
        return self._dict.get(key, default)

    def items(self):
        return self._dict.items()

    def keys(self):
        return self._dict.keys()

    def values(self):
        return self._dict.values()

    def __repr__(self) -> str:
        return f"<{self.__class__.__name__}, {self._dict}>"

    def __eq__(self, __o: object) -> bool:
        return self._dict == __o

    def __hash__(self):
        if self._hash is None:
            h = 0
            for key, value in self._dict.items():
                h ^= hash((key, value))
            self._hash = h
        return self._hash
