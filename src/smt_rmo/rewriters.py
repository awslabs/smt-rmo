# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, Callable, Iterable, List

from pysmt.environment import Environment, get_env
from pysmt.fnode import FNode


def _equal_after_normalization(formula1: FNode, formula2: FNode) -> bool:
    fresh_formula_manager = Environment().formula_manager
    formula1_normalized = fresh_formula_manager.normalize(formula1)
    formula2_normalized = fresh_formula_manager.normalize(formula2)
    return formula1_normalized == formula2_normalized


class Rewriter(ABC):
    def __init__(self, name: str = "") -> None:
        super().__init__()
        self._name: str = str(name)
        self.__applied: bool = False

    @abstractmethod
    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        raise NotImplementedError

    def feedback(self, accepted: bool) -> None:
        pass

    def applied(self) -> bool:
        return self.__applied

    def apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = None,
        **kwArgs,
    ) -> FNode:
        self.__applied = True

        if formula is None:
            return None

        if environment is not None:
            formula_manager = environment.formula_manager
            formula = formula_manager.normalize(formula)
            if args is not None:
                args = [environment.formula_manager.normalize(a) for a in args]

        if args is None:
            args = formula.args()

        return self._apply(formula, args, environment, **kwArgs)

    def __call__(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = None,
        **kwArgs,
    ) -> Any:
        return self.apply(formula, args, environment, **kwArgs)

    def __repr__(self) -> str:
        return f"Rewriter({self._name})"

    def __str__(self) -> str:
        return self.__repr__()

    def then(self, *nextRewriters: Rewriter) -> ThenRewriter:
        return ThenRewriter(self, *nextRewriters)

    def checked(self, accept_function: Callable[[FNode], bool]) -> CheckedRewriter:
        return CheckedRewriter(self, accept_function)

    def orElse(self, other: Rewriter) -> OrElseRewriter:
        return OrElseRewriter(self, other)

    def repeat(self, max_repetitions: int = -1) -> RepeatRewriter:
        return RepeatRewriter(self, max_repetitions)

    def mask_exception(
        self,
    ) -> MaskExceptionRewriter:
        return MaskExceptionRewriter(self)

    def guarded(
        self,
        applies_to: Callable[[FNode, Iterable[FNode]], bool],
        raise_exception_if_not_applicable: bool = False,
    ) -> GuardedRewriter:
        return GuardedRewriter(self, applies_to, raise_exception_if_not_applicable)


class NoneRewriter(Rewriter):
    def __init__(self) -> None:
        super().__init__("NoneRewriter")

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        return None


class ThenRewriter(Rewriter):
    def __init__(self, first_rewriter: Rewriter, *other_rewriters: List[Rewriter]) -> None:
        super().__init__()
        self._first = first_rewriter
        self._others = other_rewriters

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        res = self._first(formula, args, environment, **kwArgs)
        for r in self._others:
            if res is None:
                return None  # short circuit
            res = r(res, None, environment, **kwArgs)
        return res

    def feedback(self, accepted: bool) -> None:
        self._first.feedback(accepted)
        for o in self._others:
            o.feedback(accepted)

    def __repr__(self) -> str:
        return f"Then[{', '.join([str(r) for r in (self._first,) + self._others])}]"


class CheckedRewriter(Rewriter):
    def __init__(self, inner_rewriter: Rewriter, accept_function: Callable[[FNode], bool]) -> None:
        self._inner_rewriter = inner_rewriter
        self._accept_function = accept_function

    def accept(self, formula: FNode) -> bool:
        return self._accept_function(formula)

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        candidate = self._inner_rewriter.apply(formula, args, environment, **kwArgs)
        if self.accept(candidate):
            return candidate
        else:
            return None

    def feedback(self, accepted: bool) -> None:
        self._inner_rewriter.feedback(accepted)

    def __repr__(self) -> str:
        return f"Checked[{str(self._inner_rewriter)}]"


class OrElseRewriter(Rewriter):
    def __init__(self, or_rewriter: Rewriter, else_rewriter: Rewriter) -> None:
        self._or_rewriter: Rewriter = or_rewriter
        self._else_rewriter: Rewriter = else_rewriter
        self._or_applied: bool = False
        self._else_applied: bool = False

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        self._or_applied, self._else_applied = False, False
        candidate = self._or_rewriter.apply(formula, args, environment, **kwArgs)
        if candidate is None:
            candidate = self._else_rewriter.apply(formula, args, environment, **kwArgs)
            self._else_applied = True
        else:
            self._or_applied = True
        return candidate

    def feedback(self, accepted: bool) -> None:
        if self._or_applied:
            self._or_rewriter.feedback(accepted)
        if self._else_applied:
            self._else_rewriter.feedback(accepted)

    def __repr__(self) -> str:
        return f"OrElse({str(self._or_rewriter)}, {str(self._else_rewriter)})"


class RepeatRewriter(Rewriter):
    def __init__(self, inner_rewriter: Rewriter, max_repetitions: int = -1) -> None:
        super().__init__()
        self._inner_rewriter: Rewriter = inner_rewriter
        self._max_repetitions: int = max_repetitions

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        res = formula
        num_repetitions = 0
        while self._max_repetitions < 0 or num_repetitions < self._max_repetitions:
            candidate = self._inner_rewriter.apply(formula, args, environment, **kwArgs)
            if candidate is None or candidate == res or _equal_after_normalization(res, candidate):
                break
            res, args = candidate, candidate.args()
        return res

    def feedback(self, accepted: bool) -> None:
        self._inner_rewriter.feedback(accepted)

    def __repr__(self) -> str:
        return f"Repeat[{str(self._inner_rewriter)}, max_repetitions={'oo' if self._max_repetitions < 0 else str(self._max_repetitions)}]"


class MaskExceptionRewriter(Rewriter):
    def __init__(self, inner_rewriter: Rewriter) -> None:
        super().__init__()
        self._inner_rewriter: Rewriter = inner_rewriter

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        try:
            candidate = self._inner_rewriter.apply(formula, args, environment, **kwArgs)
            if candidate is None:
                return formula
            return candidate

        except Exception as e:
            print(e)
            return formula

    def feedback(self, accepted: bool) -> None:
        self._inner_rewriter.feedback(accepted)

    def __repr__(self) -> str:
        return f"MaskException[{str(self._inner_rewriter)}]"


class GuardedRewriter(Rewriter):
    def __init__(
        self,
        inner_rewriter: Rewriter,
        applies_to: Callable[[FNode, Iterable[FNode], Environment], bool],
        raise_exception_if_not_applicable: bool = False,
        name: str = "",
    ) -> None:
        super().__init__()
        assert callable(applies_to)
        self.__applies_to: Callable[[FNode, Iterable[FNode], Environment], bool] = applies_to
        self._raise_exception_if_not_applicable: bool = raise_exception_if_not_applicable
        self._inner_rewriter: Rewriter = inner_rewriter
        self._inner_applied: bool = False

    def applies_to(self, node: FNode, args: Iterable[FNode], env: Environment) -> bool:
        return self.__applies_to(node, args, env)

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        self._inner_applied = False
        if self.applies_to(formula, args, environment):
            self._inner_applied = True
            return self._inner_rewriter(formula, args, environment, **kwArgs)
        else:
            if self._raise_exception_if_not_applicable:
                raise Exception(f"Rewriter {str(self)} cannot be applied to:\n{str(formula)}")
            return formula

    def feedback(self, accepted: bool) -> None:
        if self._inner_applied:
            self._inner_rewriter.feedback(accepted)

    def __repr__(self) -> str:
        return f"Guarded[{str(self._inner_rewriter)}]"


class LambdaRewriter(Rewriter):
    def __init__(
        self,
        apply: Callable[[FNode, Iterable[FNode], Environment], FNode],
        name: str = "",
    ) -> None:
        super().__init__(name=f"Lambda({str(name)})")
        assert callable(apply)
        self.__apply: Callable[[FNode, Iterable[FNode], Environment], FNode] = apply

    def _apply(
        self,
        formula: FNode,
        args: Iterable[FNode] = None,
        environment: Environment = get_env(),
        **kwArgs,
    ) -> FNode:
        """Notice that additional kwArgs are not propagated by the LambdaRewriter. Consider extending Rewriter
        for more flexibility"""
        return self.__apply(formula, args, environment)


class _IdentityRewriter(LambdaRewriter):
    def __init__(self) -> None:
        super().__init__(lambda f, args, env: f, name="identity")


IdentityRewriter = _IdentityRewriter()


def AnyRewriter(*rewriters) -> Rewriter:
    """Constructs a tree of OrElse rewriters for a collection of rewriters. It applies
    the rewriters in order until the first one succeeds. Returns None if no rewriter succeeds
    """
    if len(rewriters) == 0:
        return NoneRewriter()
    if len(rewriters) == 1:
        return rewriters[0]

    return OrElseRewriter(rewriters[0], AnyRewriter(*rewriters[1:]))
