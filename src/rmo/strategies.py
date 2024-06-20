from abc import ABC, abstractmethod
from collections import deque
from typing import Callable, Dict, Iterable, List, Set

from pysmt.environment import Environment, get_env
from pysmt.fnode import FNode
from pysmt.oracles import SizeOracle
from pysmt.walkers import IdentityDagWalker

from rmo.rewriters import Rewriter
from rmo.utils import InfiniteTimeoutBudget, TimeoutBudget, track_timeout_budget


class Visitor(ABC):
    @abstractmethod
    def visit(self, formula: FNode, **kwArgs) -> None:
        raise NotImplementedError()


class BFSGlobalVisitor(Visitor):
    def __init__(
        self,
        rewriter: Rewriter,
        oracle: Callable[[FNode], bool],
        environment: Environment = get_env(),
        timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
    ) -> None:
        super().__init__()
        self._rewriter: Rewriter = rewriter
        self._oracle: Callable[[FNode], bool] = oracle
        self._environment: Environment = environment
        self._timeout_budget: TimeoutBudget = timeout_budget

    def visit(self, formula: FNode, **kwArgs) -> None:
        queue = deque()
        queue.append(formula)

        while queue and self._timeout_budget.available():
            with track_timeout_budget(self._timeout_budget):
                expr = queue.popleft()
                candidate_replacement = self._rewriter(expr, environment=self._environment)

                accepted = False
                if candidate_replacement is not None and candidate_replacement != expr:
                    formula_tmp = self._environment.substituter.substitute(
                        formula, {expr: candidate_replacement}, None
                    )
                    if self._oracle(formula_tmp):
                        accepted = True
                        formula = formula_tmp
                        self._rewriter.feedback(True)
                    else:
                        self._rewriter.feedback(False)

                if accepted:
                    for c in candidate_replacement.args():
                        queue.append(c)
                else:
                    for c in expr.args():
                        queue.append(c)

        return formula


class NodeReplacerDagWalker(IdentityDagWalker):
    def __init__(self, target_node, replacement, env=None, invalidate_memoization=None):
        super().__init__(env, invalidate_memoization)
        self.memoization[target_node] = replacement

    def walk_bv_extract(self, formula, args, **kwargs):
        if (
            formula.bv_extract_start() == 0
            and formula.bv_extract_end() - formula.bv_extract_start() + 1 > formula.bv_width()
        ):
            return formula

        return self.mgr.BVExtract(
            args[0],
            start=formula.bv_extract_start(),
            end=min(formula.bv_extract_end(), args[0].bv_width() - 1),
        )


class BFSLocalVisitor(Visitor):
    def __init__(
        self,
        rewriters: Iterable[Rewriter],
        oracle: Callable[[FNode], bool],
        always_simplify: bool = False,
        environment: Environment = get_env(),
        timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
    ) -> None:
        super().__init__()
        self._rewriters: Rewriter = list(rewriters)
        self._oracle: Callable[[FNode], bool] = oracle
        self._always_simplify: bool = always_simplify
        self._environment: Environment = environment
        self._timeout_budget: TimeoutBudget = timeout_budget

    def visit(self, formula: FNode, **kwArgs) -> None:
        queue = deque()
        queue.append((formula, None, None))

        while queue and self._timeout_budget.available():
            expr, parent, pos = queue.popleft()

            for rewriter in self._rewriters:
                if not self._timeout_budget.available():
                    break

                with track_timeout_budget(self._timeout_budget):
                    candidate_replacement = rewriter(expr, environment=self._environment)

                    accepted = False

                    if candidate_replacement is not None and candidate_replacement != expr:
                        candidate_formula = NodeReplacerDagWalker(
                            expr, candidate_replacement, self._environment
                        ).walk(formula)

                        if self._always_simplify:
                            simplified = self._environment.simplifier.simplify(candidate_formula)
                            if self._oracle(simplified):
                                formula = simplified
                                accepted = True

                        if not accepted:
                            if self._oracle(candidate_formula):
                                formula = candidate_formula
                                accepted = True

                rewriter.feedback(accepted)
                if accepted:
                    break

            if accepted:
                for i, c in enumerate(candidate_replacement.args()):
                    queue.append((c, candidate_replacement, i))
            else:
                for i, c in enumerate(expr.args()):
                    queue.append((c, expr, i))

        return formula


class BFSGreedyLocalBestVisitor(Visitor):
    def __init__(
        self,
        rewriters: Iterable[Rewriter],
        oracle: Callable[[FNode], bool],
        environment: Environment = get_env(),
        timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
    ) -> None:
        super().__init__()
        self._rewriters: List[Rewriter] = list(rewriters)
        self._oracle: Callable[[FNode], bool] = oracle
        self._environment: Environment = environment
        self._timeout_budget: TimeoutBudget = timeout_budget

    def visit(self, formula: FNode, **kwArgs) -> None:
        queue = deque()
        queue.append((formula, None, None))

        while queue and self._timeout_budget.available():
            with track_timeout_budget(self._timeout_budget):
                expr, parent, pos = queue.popleft()

                size_oracle = SizeOracle()
                rejection_score = -1_000_000

                initial_size = max(size_oracle.get_size(expr), 1)
                candidate_formulas = [
                    NodeReplacerDagWalker(
                        expr,
                        rewriter(expr, environment=self._environment),
                        self._environment,
                    ).walk(formula)
                    for rewriter in self._rewriters
                ]
                score = [
                    (
                        (initial_size - size_oracle.get_size(f)) / initial_size
                        if self._oracle(f)
                        else rejection_score
                    )
                    for f in candidate_formulas
                ]

                best_candidate, best_score = expr, 0
                for i, s in enumerate(score):
                    # self._rewriters[i].feedback(s != rejection_score)
                    if s > best_score:
                        best_candidate, best_score = candidate_formulas[i], s

                for i, c in enumerate(best_candidate.args()):
                    queue.append((c, best_candidate, i))

        return formula


class BFSLocalVisitorWithMemory(Visitor):
    def __init__(
        self,
        rewriters: Iterable[Rewriter],
        oracle: Callable[[FNode], bool],
        environment: Environment = get_env(),
        timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
    ) -> None:
        super().__init__()
        self._rewriters: Rewriter = list(rewriters)
        self._oracle: Callable[[FNode], bool] = oracle
        self._environment: Environment = environment
        self._timeout_budget: TimeoutBudget = timeout_budget
        self._already_attempted: Dict[FNode, Set[Rewriter]] = {}

    def visit(self, formula: FNode, **kwArgs) -> None:
        queue = deque()
        queue.append((formula, None, None))

        while queue and self._timeout_budget.available():
            with track_timeout_budget(self._timeout_budget):
                expr, parent, pos = queue.popleft()

                if expr not in self._already_attempted:
                    self._already_attempted[expr] = set()

                rewriters_not_yet_applied = [
                    r for r in self._rewriters if r not in self._already_attempted[expr]
                ]

                for rewriter in rewriters_not_yet_applied:  # self._rewriters:
                    self._already_attempted[expr].add(rewriter)

                    candidate_replacement = rewriter(expr, environment=self._environment)

                    accepted = False

                    if candidate_replacement is not None and candidate_replacement != expr:
                        if parent is None:
                            # replacing the formula
                            if self._oracle(candidate_replacement):
                                formula = candidate_replacement
                                accepted = True

                        else:
                            candidate_formula = NodeReplacerDagWalker(
                                expr, candidate_replacement, self._environment
                            ).walk(formula)

                            if self._oracle(candidate_formula):
                                formula = candidate_formula
                                accepted = True

                    rewriter.feedback(accepted)
                    if accepted:
                        break

                if accepted:
                    for i, c in enumerate(candidate_replacement.args()):
                        queue.append((c, candidate_replacement, i))
                else:
                    for i, c in enumerate(expr.args()):
                        queue.append((c, expr, i))

        return formula
