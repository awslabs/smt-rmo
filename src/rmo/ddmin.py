from collections import deque
from typing import Any, Callable, Dict, Iterable, List

from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.smtlib.script import SmtLibScript

from rmo.rewriters import Rewriter
from rmo.utils import InfiniteTimeoutBudget, TimeoutBudget, track_timeout_budget


def ddmin_script(
    script: SmtLibScript,
    script_oracle,
    timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
):
    children = list(script.commands)
    n = 2
    while len(children) >= 2 and timeout_budget.available():
        start = 0
        subset_length = int(len(children) / n)
        some_complement_satisfies_oracle = False

        while start < len(children) and timeout_budget.available():
            with track_timeout_budget(timeout_budget):
                complement = children[: int(start)] + children[int(start + subset_length) :]

                res = SmtLibScript()
                for cmd in complement:
                    res.add_command(cmd)

                if script_oracle(res):
                    children = complement
                    n = max(n - 1, 2)
                    some_complement_satisfies_oracle = True
                    break

                start += subset_length

        if not some_complement_satisfies_oracle:
            if n == len(children):
                break
            n = min(n * 2, len(children))

    res = SmtLibScript()
    for cmd in children:
        res.add_command(cmd)

    return res


def ddmin_assertions(
    assertion_to_formula,
    a2f_oracle,
    timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
):
    children = list(sorted(assertion_to_formula.keys()))
    n = 2
    while len(children) >= 2 and timeout_budget.available():
        start = 0
        subset_length = int(len(children) / n)
        some_complement_satisfies_oracle = False

        while start < len(children) and timeout_budget.available():
            with track_timeout_budget(timeout_budget):
                complement = children[: int(start)] + children[int(start + subset_length) :]

                to_remove = set(assertion_to_formula.keys()) - set(complement)
                candidate_a2f = dict(assertion_to_formula)
                for i in to_remove:
                    candidate_a2f[i] = None

                if a2f_oracle(candidate_a2f):
                    children = complement
                    n = max(n - 1, 2)
                    some_complement_satisfies_oracle = True
                    break

                start += subset_length

        if not some_complement_satisfies_oracle:
            if n == len(children):
                break
            n = min(n * 2, len(children))

    to_remove = set(assertion_to_formula.keys()) - set(children)
    candidate_a2f = dict(assertion_to_formula)
    for i in to_remove:
        candidate_a2f[i] = None
    return candidate_a2f


class DDMinRewriter(Rewriter):
    def __init__(
        self,
        assertion_to_formula: Dict[Any, FNode],
        target_command: Any,
        oracle: Callable[[FNode], bool],
        guard: Callable[[FNode], bool],
        constructor: Callable[[List[FNode]], FNode],
        name: str = "",
    ) -> None:
        super().__init__(name="DDMinRewriter" if name == "" else str(name))
        self._assertion_to_formula: Dict[Any, FNode] = assertion_to_formula
        self._target_command: Any = target_command
        self._oracle: Callable[[FNode], bool] = oracle
        self._guard: Callable[[FNode], bool] = guard
        self._constructor: Callable[[List[FNode]], FNode] = constructor
        self._target_formula = self._assertion_to_formula[self._target_command]

    def _minimize(self, target_formula, node, args, constructor, oracle, environment):
        children = list(args)
        n = 2
        while len(children) >= 2:
            start = 0
            subset_length = int(len(children) / n)
            some_complement_satisfies_oracle = False

            while start < len(children):
                complement = children[: int(start)] + children[int(start + subset_length) :]

                replacement_expression = constructor(complement)
                complement_problem = environment.substituter.substitute(
                    target_formula, {node: replacement_expression}, None
                )

                a2f = dict(self._assertion_to_formula)
                a2f[self._target_command] = complement_problem

                if oracle(a2f):
                    children = complement
                    n = max(n - 1, 2)
                    some_complement_satisfies_oracle = True
                    break

                start += subset_length

            if not some_complement_satisfies_oracle:
                if n == len(children):
                    break
                n = min(n * 2, len(children))

        return constructor(children)

    def set_target_formula(self, target_formula: FNode) -> None:
        self._target_formula = target_formula

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = None,
        **kwArgs,
    ) -> FNode:
        if environment is not None:
            assert (
                self._constructor.__self__ == environment.formula_manager
            ), "The constructor function is not compatible with the formula manager of the environment passed as argument"

        if not self._guard(formula):
            return None

        target_formula = self._target_formula

        if environment is not None:
            target_formula = environment.formula_manager.normalize(target_formula)
            formula = environment.formula_manager.normalize(formula)
            if args is not None:
                args = [environment.formula_manager.normalize(a) for a in args]

        args = args if args is not None else formula.args()

        return self._minimize(
            self._target_formula,
            formula,
            args,
            self._constructor,
            self._oracle,
            environment,
        )


class BFSDDMinTraverser:
    def __init__(
        self,
        rewriters: Iterable[DDMinRewriter],
        environment: Environment = Environment(),
        timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
    ) -> None:
        if len(rewriters) == 1 and hasattr(rewriters[0], "__iter__"):
            rewriters = list(rewriters[0])

        assert all(isinstance(r, DDMinRewriter) for r in rewriters)
        self._rewriters: List[DDMinRewriter] = list(rewriters)
        self._environment: Environment = environment
        self._timeout_budget: TimeoutBudget = timeout_budget

    def visit(self, formula: FNode, **kwArgs) -> None:
        formula = self._environment.formula_manager.normalize(formula)
        queue = deque()
        queue.append(formula)

        while queue and self._timeout_budget.available():
            with track_timeout_budget(self._timeout_budget):
                expr = queue.popleft()

                any_replaced = False
                for rewriter in self._rewriters:
                    candidate_replacement = rewriter(expr, environment=self._environment)
                    if candidate_replacement is not None and candidate_replacement != expr:
                        any_replaced = True
                        formula = self._environment.substituter.substitute(
                            formula, {expr: candidate_replacement}, None
                        )
                        for r in self._rewriters:
                            r.set_target_formula(formula)
                        for c in candidate_replacement.args():
                            queue.append(c)
                        break

                if not any_replaced:
                    for c in expr.args():
                        queue.append(c)

        return formula
