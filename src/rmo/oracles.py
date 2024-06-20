from __future__ import annotations

import copy
import json
import logging
import os
import random
import re
import signal
import sys
import tempfile
from abc import ABC
from enum import Enum
from io import StringIO
from typing import Any, Callable, Union

from pysmt.logics import get_closer_smtlib_logic
from pysmt.oracles import get_logic
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand, SmtLibScript

from rmo import distributionCompare
from rmo.executors import SolverExecutor, SolverOutput

DefaultMetric: dict = {}
with open(
    str(os.path.dirname(os.path.abspath(__file__))) + "/z3DefaultMetric.json",
    "r",
) as f:
    DefaultMetric["z3"] = json.load(f)
with open(
    str(os.path.dirname(os.path.abspath(__file__))) + "/cvc5DefaultMetric.json",
    "r",
) as f:
    DefaultMetric["cvc5"] = json.load(f)
with open(
    str(os.path.dirname(os.path.abspath(__file__))) + "/cvc4DefaultMetric.json",
    "r",
) as f:
    DefaultMetric["cvc4"] = json.load(f)
logger = logging.getLogger(__name__)


class Oracle(ABC):
    def __init__(self, check_function: Callable[[SmtLibScript], bool]) -> None:
        self.num_check = 0
        self.num_true_check = 0
        assert isinstance(check_function, Callable)
        self._check_function: Callable[[SmtLibScript], bool] = check_function

    def check(self, formula: SmtLibScript) -> bool:
        """Returns true iff bug is preserved"""
        self.num_check += 1
        res = self._check_function(formula)
        if res:
            self.num_true_check += 1
        return res

    def as_soft_predicate(self):
        """Returns soft predicate based on check"""
        return SoftPredicate(lambda e: float(self.check(e)))

    def __call__(self, formula: SmtLibScript, **kwds: Any) -> bool:
        return self.check(formula)

    def __or__(self, __t: Oracle) -> Oracle:
        """self | __t"""
        assert isinstance(__t, Oracle)
        return Oracle(lambda e: self.check(e) or __t.check(e))

    def __and__(self, __t: Oracle) -> Oracle:
        """self & __t"""
        assert isinstance(__t, Oracle)
        return Oracle(lambda e: self.check(e) and __t.check(e))

    def __xor__(self, __t: Oracle) -> Oracle:
        """self ^ __t"""
        assert isinstance(__t, Oracle)
        return Oracle(lambda e: self.check(e) ^ __t.check(e))

    def __rand__(self, __r: Oracle) -> Oracle:
        return self.__and__(__r)

    def __ror__(self, __t: Oracle) -> Oracle:
        return self.__or__(__t)

    def __rxor__(self, __t: Oracle) -> Oracle:
        return self.__xor__(__t)

    def __neg__(self) -> Oracle:
        """~ self"""
        return Oracle(lambda e: not self.check(e))

    def __invert__(self) -> Oracle:
        return self.__neg__()


class SoftPredicate(ABC):
    def __init__(self, check_function: Callable[[SmtLibScript], float]) -> None:
        self.num_check = 0
        assert isinstance(check_function, Callable)
        self._check_function: Callable[[SmtLibScript], float] = check_function

    def get_score(self, formula: SmtLibScript) -> float:
        """Returns the soft oracle's score"""
        res = self._check_function(formula)
        assert 0 <= res, "Soft oracle's score is not in the legal range"
        return res

    def soft_predicate_to_oracle(
        self, lower_bound: float = None, upper_bound: float = None
    ) -> Oracle:
        """Returns an oracle that accepts when the score of this soft predicate is within
        [lower_bound, upper_bound], inclusive. At least one of the bounds must be defined.
        """
        assert (
            lower_bound is not None or upper_bound is not None
        ), "At least one of the bounds should be specified"
        lower_bound = 0.0 if lower_bound is None else float(lower_bound)
        upper_bound = 1.0 if upper_bound is None else float(upper_bound)
        return Oracle(lambda e: lower_bound <= self.get_score(e) <= upper_bound)

    def __call__(self, formula: SmtLibScript, **kwds: Any) -> float:
        return self.get_score(formula)

    def __or__(self, __t) -> SoftPredicate:
        """self | __t but fuzzy"""
        assert isinstance(__t, SoftPredicate)
        return SoftPredicate(lambda e: max(self.get_score(e), __t.get_score(e)))

    def __and__(self, __t) -> SoftPredicate:
        """self & __t but fuzzy"""
        assert isinstance(__t, SoftPredicate)
        return SoftPredicate(lambda e: min(self.get_score(e), __t.get_score(e)))

    def __rand__(self, __r) -> SoftPredicate:
        return self.__and__(__r)

    def __ror__(self, __t) -> SoftPredicate:
        return self.__or__(__t)

    def __neg__(self) -> SoftPredicate:
        """~ self"""
        return SoftPredicate(lambda e: 1 - self.get_score(e))

    def __invert__(self) -> SoftPredicate:
        return self.__neg__()


############### Some trivial oracles #################


class TrueOracle(Oracle):
    def __init__(self) -> None:
        super().__init__(lambda e: True)


class FalseOracle(Oracle):
    def __init__(self) -> None:
        super().__init__(lambda e: False)


class RandomOracle(Oracle):
    def __init__(self) -> None:
        super().__init__(lambda e: random.randint(0, 1) == 0)


############## Execution oracles ###################


class ExecutionOracle(Oracle):
    def __init__(
        self,
        executor: SolverExecutor,
        check_output_function: Callable[[SolverOutput], bool],
        timeout_secs: float = -1.0,
        num_trials: int = 5,
    ) -> None:
        def _check_script(formula: SmtLibScript) -> bool:
            execution_output = None
            for _ in range(num_trials):
                execution_output = executor.run_solver(formula, timeout_seconds=timeout_secs)
                if execution_output is not None:
                    break

            return check_output_function(execution_output)

        super().__init__(_check_script)


class DifferentialExectionOracle(Oracle):
    def __init__(
        self,
        executor1: SolverExecutor,
        executor2: SolverExecutor,
        compare_output_function: Callable[[SolverOutput, SolverOutput], bool],
        timeout_secs_executor1: float = -1.0,
        timeout_secs_executor2: float = -1.0,
        num_trials_executor1: int = 5,
        num_trials_executor2: int = 5,
    ) -> None:
        def _check_script(formula: SmtLibScript) -> bool:
            execution_output1 = None
            for _ in range(num_trials_executor1):
                execution_output1 = executor1.run_solver(
                    formula, timeout_seconds=timeout_secs_executor1
                )
                if execution_output1 is not None:
                    break

            execution_output2 = None
            for _ in range(num_trials_executor2):
                execution_output2 = executor2.run_solver(
                    formula, timeout_seconds=timeout_secs_executor2
                )
                if execution_output2 is not None:
                    break

            return compare_output_function(execution_output1, execution_output2)

        super().__init__(_check_script)


################## Some common execution and differential execution oracles ###############


class OutputRegexExecutionOracle(ExecutionOracle):
    """Checks if stdout/stderr contain given regex"""

    def __init__(
        self,
        executor: SolverExecutor,
        re_pattern: Union[str, re.Pattern],
        check_stdout: bool = True,
        check_stderr: bool = True,
        timeout_secs: float = -1.0,
        num_trials: int = 5,
    ) -> None:
        assert (
            check_stderr or check_stdout
        ), "At least one between stderr and stdout should be checked"
        assert isinstance(num_trials, int) and num_trials > 0
        assert isinstance(re_pattern, re.Pattern) or isinstance(re_pattern, str)

        _match = re_pattern if isinstance(re_pattern, re.Pattern) else re.compile(re_pattern)

        def _check(execution_output: SolverOutput) -> bool:
            if execution_output is not None:
                # no timeout occurred
                if check_stdout:
                    res = next(_match.finditer(execution_output.stdout), None) is not None
                    if res:
                        return res

                if check_stderr:
                    return next(_match.finditer(execution_output.stderr), None) is not None
            return False

        super().__init__(executor, _check, timeout_secs, num_trials)


class TimeoutExecutionOracle(ExecutionOracle):
    """Returns true if the execution timed out"""

    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float,
        num_trials: int = 1,
    ) -> None:
        timeout_secs = float(timeout_secs)
        assert timeout_secs > 0
        assert isinstance(num_trials, int) and num_trials > 0

        super().__init__(executor, lambda r: r is None, timeout_secs, num_trials)


class IsSatExecutionOracle(OutputRegexExecutionOracle):
    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1.0,
        num_trials: int = 5,
    ) -> None:
        super().__init__(
            executor,
            re_pattern=re.compile("^\(\s*sat\s*\)|^\s*sat\s*", re.IGNORECASE),
            check_stdout=True,
            check_stderr=False,
            timeout_secs=timeout_secs,
            num_trials=num_trials,
        )


class IsUnsatExecutionOracle(OutputRegexExecutionOracle):
    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1.0,
        num_trials: int = 5,
    ) -> None:
        super().__init__(
            executor,
            re_pattern=re.compile("^\(\s*unsat\s*\)|^\s*unsat\s*", re.IGNORECASE),
            check_stdout=True,
            check_stderr=False,
            timeout_secs=timeout_secs,
            num_trials=num_trials,
        )


class IsUnknownExecutionOracle(OutputRegexExecutionOracle):
    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1.0,
        num_trials: int = 5,
    ) -> None:
        super().__init__(
            executor,
            re_pattern=re.compile("\(\s*unknown\s*\)", re.IGNORECASE),
            check_stdout=True,
            check_stderr=False,
            timeout_secs=timeout_secs,
            num_trials=num_trials,
        )


class CheckReturnSignalExecutionOracle(ExecutionOracle):
    def __init__(
        self,
        executor: SolverExecutor,
        desired_signal: int,
        timeout_secs: float = -1,
        num_trials: int = 5,
    ) -> None:
        def _check(execution_output: SolverOutput) -> bool:
            return execution_output is not None and execution_output.return_code == desired_signal

        super().__init__(executor, _check, timeout_secs, num_trials)


class SegFaultExecutionOracle(CheckReturnSignalExecutionOracle):
    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1,
        num_trials: int = 5,
    ) -> None:
        super().__init__(executor, -signal.SIGSEGV, timeout_secs, num_trials)


############# Some common differential oracles ############


class InconsistentSatDifferentialOracle(DifferentialExectionOracle):
    """Compares stdout and/or stderr between two solvers, returns False if either timed out"""

    def __init__(
        self,
        executor1: SolverExecutor,
        executor2: SolverExecutor,
        timeout_secs_executor1: float = -1.0,
        timeout_secs_executor2: float = -1.0,
        num_trials_executor1: int = 5,
        num_trials_executor2: int = 5,
        preserve_initial_inconsistency: bool = False,
    ) -> None:
        assert isinstance(num_trials_executor1, int) and num_trials_executor1 > 0
        assert isinstance(num_trials_executor2, int) and num_trials_executor2 > 0

        Decision = Enum("Decision", ["sat", "unsat", "unknown"])

        self._initial_solver1_decision: Decision = None
        self._initial_solver2_decision: Decision = None
        self._preserve_initial_inconsistecy: bool = preserve_initial_inconsistency

        def output_to_decision(output: str) -> Decision:
            if output.startswith("unsat"):
                return Decision.unsat
            elif output.startswith("sat"):
                return Decision.sat
            elif output.startswith("unknown"):
                return Decision.unknown

            return None

        def _compare(executor_output1: SolverOutput, executor_output2: SolverOutput) -> bool:
            if executor_output1 is None or executor_output2 is None:
                # At least one of the solvers did not return an output (timeout)
                return False

            solver1_decision: Decision = output_to_decision(executor_output1.stdout)
            assert (
                solver1_decision is not None
            ), f"Cannot parse decision from Solver1 output:\n{executor_output1.stdout}"

            solver2_decision: Decision = output_to_decision(executor_output2.stdout)
            assert (
                solver2_decision is not None
            ), f"Cannot parse decision from Solver2 output:\n{executor_output2.stdout}"

            if self._preserve_initial_inconsistecy:
                # The oracle checks that the very inconsistency detected on the initial input (e.g., Solver1=sat and Solver2=unknwon) is preserved
                if self._initial_solver1_decision is None:
                    # first execution, which is assumed to happen on the initial input file passed to RMO
                    assert self._initial_solver2_decision is None
                    assert (
                        solver1_decision != solver2_decision
                    ), f"The initial input did not produce inconsistent results. Solver1 returned: {solver1_decision.name} and Solver2 returned {solver2_decision.name}"

                    (
                        self._initial_solver1_decision,
                        self._initial_solver2_decision,
                    ) = (
                        solver1_decision,
                        solver2_decision,
                    )

                return (
                    solver1_decision == self._initial_solver1_decision
                    and solver2_decision == self._initial_solver2_decision
                )

            else:
                # The oracle just cheks the two solvers produced different decisions
                return solver1_decision != solver2_decision

        super().__init__(
            executor1,
            executor2,
            _compare,
            timeout_secs_executor1,
            timeout_secs_executor2,
            num_trials_executor1,
            num_trials_executor2,
        )


class SameOutputDifferentialOracle(DifferentialExectionOracle):
    """Compares stdout and/or stderr between two solvers, returns False if either timed out"""

    def __init__(
        self,
        executor1: SolverExecutor,
        executor2: SolverExecutor,
        compare_stdout: bool = False,
        compare_stderr: bool = True,
        timeout_secs_executor1: float = -1.0,
        timeout_secs_executor2: float = -1.0,
        num_trials_executor1: int = 5,
        num_trials_executor2: int = 5,
        true_if_different: bool = True,
    ) -> None:
        assert (
            compare_stdout or compare_stderr
        ), "At least one between stderr and stdout should be compared"
        assert isinstance(num_trials_executor1, int) and num_trials_executor1 > 0
        assert isinstance(num_trials_executor2, int) and num_trials_executor2 > 0

        def _compare(executor_output1: SolverOutput, executor_output2: SolverOutput) -> bool:
            if executor_output1 is None or executor_output2 is None:
                # At least one of the solvers did not return an output (timeout)
                return False

            output_is_the_same = (
                executor_output1.stdout == executor_output2.stdout if compare_stdout else True
            )
            output_is_the_same = output_is_the_same and (
                executor_output1.stderr == executor_output2.stderr if compare_stderr else True
            )

            return output_is_the_same ^ true_if_different

        super().__init__(
            executor1,
            executor2,
            _compare,
            timeout_secs_executor1,
            timeout_secs_executor2,
            num_trials_executor1,
            num_trials_executor2,
        )


class XorTimeoutDifferentialExecutionOracle(DifferentialExectionOracle):
    """Returns true if either both or none of the solvers time out"""

    def __init__(
        self,
        executor1: SolverExecutor,
        executor2: SolverExecutor,
        timeout_secs_executor1: float = -1.0,
        timeout_secs_executor2: float = -1.0,
        num_trials_executor1: int = 5,
        num_trials_executor2: int = 5,
    ) -> None:
        assert isinstance(num_trials_executor1, int) and num_trials_executor1 > 0
        assert isinstance(num_trials_executor2, int) and num_trials_executor2 > 0

        def _compare(execution_output1: SolverOutput, execution_output2: SolverOutput) -> bool:
            return (execution_output1 is None and execution_output2 is None) or (
                execution_output1 is not None and execution_output2 is not None
            )

        super().__init__(
            executor1,
            executor2,
            _compare,
            timeout_secs_executor1,
            timeout_secs_executor2,
            num_trials_executor1,
            num_trials_executor2,
        )


class TimeoutRegressionDifferentialExecutionOracle(DifferentialExectionOracle):
    """Returns true if either both or none of the solvers time out"""

    def __init__(
        self,
        executor1: SolverExecutor,
        executor2: SolverExecutor,
        timeout_secs_executor1: float = -1.0,
        timeout_secs_executor2: float = -1.0,
        num_trials_executor1: int = 5,
        num_trials_executor2: int = 5,
    ) -> None:
        assert isinstance(num_trials_executor1, int) and num_trials_executor1 > 0
        assert isinstance(num_trials_executor2, int) and num_trials_executor2 > 0

        def _compare(execution_output1: SolverOutput, execution_output2: SolverOutput) -> bool:
            return execution_output1 is not None and execution_output2 is None

        super().__init__(
            executor1,
            executor2,
            _compare,
            timeout_secs_executor1,
            timeout_secs_executor2,
            num_trials_executor1,
            num_trials_executor2,
        )


################# Soft oracles ###################


class StatisticsComparisonOracle(SoftPredicate):
    """return a score of distance of output distribution"""

    def get_logic(self):
        # find out what the logic is, if specified
        for cmd in self.base:
            if cmd.name == "set-logic":
                return str(cmd.args[0])
        # otherwise, see if pysmt can deduce it
        try:
            return str(
                get_closer_smtlib_logic(get_logic(self.base.get_last_formula()))
            )  # If user did not set logic, try to use pysmt to get the logic. pysmt currently has bugs
        except:  # noqa: E722
            return None

    def parse_stats(self, stat_str: str) -> dict:
        return {}

    def __init__(
        self,
        executor: SolverExecutor,
        solver_name=None,
        timeout_secs: float = -1.0,
        target_metric=None,
        metric_weight=None,
        base: SmtLibScript = None,
    ):
        assert base is not None, "You need to provide the base formula for comparison"
        assert solver_name in {
            "z3",
            "cvc4",
            "cvc5",
        }, "Do not support the given solver"
        self.solver = solver_name
        if solver_name == "z3":
            self.args = ["-st"]
        elif solver_name == "cvc5":
            self.args = ["--stats-internal"]
        elif solver_name == "cvc4":
            self.args = ["--stats"]
        self.base = base
        self.logic = self.get_logic()
        self.score = -1
        if target_metric:
            self.target_metric = target_metric
        else:
            try:
                self.target_metric = DefaultMetric[solver_name][self.logic]
            except:
                logging.log(
                    logging.INFO,
                    f"No stats found for logic {self.logic}. Using ALL for metrics",
                )
                self.target_metric = DefaultMetric[solver_name]["ALL"]
        logging.log(logging.INFO, f"Using metrics: {self.target_metric}")
        if metric_weight is None:
            self.metric_weight: dict = {}
            for metric in self.target_metric:
                self.metric_weight[metric] = 1
        else:
            self.metric_weight = metric_weight
        base_output = executor.run_solver(
            script=self.base, args=self.args, timeout_seconds=timeout_secs
        )
        if base_output is None:
            base_statistic = {}
        else:
            base_statistic = self.parse_stats(base_output.stdout + "\n" + base_output.stderr)
        if len(base_statistic) < len(self.target_metric):
            for stat in self.target_metric:
                if stat not in base_statistic.keys():
                    logging.log(
                        logging.WARN,
                        f"""The stat {stat} is not produced by the solver. This may be due to a typo in the stat name or because the benchmark doesn't expose the desired solver stat.""",
                    )

        def _check_script(formula: SmtLibScript) -> float:
            execution_output = executor.run_solver(
                script=formula, args=self.args, timeout_seconds=timeout_secs
            )
            if execution_output is None:
                new_statistic = {}
            else:
                new_statistic = self.parse_stats(
                    execution_output.stdout + "\n" + execution_output.stderr
                )
            if (new_statistic == {}) and (base_statistic == {}):
                return 0
            self.score = distributionCompare.calculate_l0_distance(new_statistic, base_statistic)
            # Now we use l0 distance and directly return the number
            return self.score

        super().__init__(_check_script)

    def check_in_metric(self, key: str):
        for metric in self.target_metric:
            if ((metric in key) and ("::" in key)) or (metric == key):
                # To handle non-complete stat attribute name in cvc4/5 (and == for z3)
                return metric
        return False


class CVC5StatisticsComparisonPredicate(StatisticsComparisonOracle):
    """return a score of distance of output distribution of CVC5"""

    def parse_stats(self, stat_str: str):
        stat_dict: dict = {}
        lines = stat_str.strip().split("\n")
        for line in lines:
            if len(line) <= 0:
                continue
            if line[0] == "(" or line[0] == ")":
                # CVC4/5 started with "(" is the model, we skip this part. Since there is no stats here
                continue
            if "{" in line and "}" in line:
                headStr = line.split("=")[0].strip()
                line = line[line.index("{") + 1 : line.index("}")].split(",")
                # For cvc5, parse the stats. The format looks like C = {"A":123, "B":321}. We store key="C{A}" and value = float(123)
                for pair in line:
                    key, value = (
                        pair[: pair.rindex(":")].strip(),
                        pair[pair.rindex(":") + 1 :].strip(),
                    )
                    key = headStr + "{" + key.strip() + "}"
                    if not self.check_in_metric(key):
                        # For each attribute, check if it's in target metric
                        continue
                    stat_dict[key.strip()] = float(value) * self.metric_weight.get(
                        self.check_in_metric(key)
                    )
            elif "=" in line and "::" in line:  # handle globalTime in cvc5
                try:
                    key, value = line.split("=")
                except:
                    continue
                if not self.check_in_metric(key):
                    continue
                while value and (not value[-1].isdigit()):  # handle "ms" in the end of xxx"ms"
                    value = value[:-1]
                if not value:
                    continue
                value = value.strip()
                key = key.strip()
                stat_dict[key] = float(value) * self.metric_weight.get(self.check_in_metric(key))
        return stat_dict

    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1.0,
        target_metric=None,
        metric_weight=None,
        base: SmtLibScript = None,
    ):
        output = executor.run_solver(
            args=["--version"], script=base, timeout_seconds=timeout_secs
        ).stdout
        assert "cvc5" in output, "You did not provide correct solver"

        super().__init__(
            executor=executor,
            timeout_secs=timeout_secs,
            target_metric=target_metric,
            metric_weight=metric_weight,
            base=base,
            solver_name="cvc5",
        )


class CVC4StatisticsComparisonPredicate(StatisticsComparisonOracle):
    """return a score of distance of output distribution of CVC4"""

    def parse_stats(self, stat_str: str):
        stat_dict: dict = {}
        lines = stat_str.strip().split("\n")
        for line in lines:
            if len(line) <= 0:
                continue
            if line[0] == "(" or line[0] == ")":
                # CVC4/5 started with "(" is the model, we skip this part. Since there is no stats here
                continue
            if "," in line and "::" in line:
                # Handle cvc4's data attributes. CVC4 stats have two formats: "[(A:123),(B:312)]" and "A, 123", we need to handle them separately
                if "[" in line and "]" in line:
                    line = line[line.index("[") + 1 : line.index("]")].split(",")
                    if len(line[0]) < 1:
                        continue
                    for pair in line:
                        key, value = pair[pair.index("(") + 1 : pair.index(")")].split(":")
                        key = key.strip()
                        if not self.check_in_metric(key):
                            continue
                        stat_dict[key.strip()] = float(value) * self.metric_weight.get(key)
                else:
                    try:
                        key, value = line.split(",")
                        if not self.check_in_metric(key):
                            continue
                        stat_dict[key.strip()] = float(value) * self.metric_weight.get(key)
                    except:
                        continue
        return stat_dict

    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1.0,
        target_metric=None,
        metric_weight=None,
        base: SmtLibScript = None,
    ):
        output = executor.run_solver(
            args=["--version"], script=base, timeout_seconds=timeout_secs
        ).stdout
        assert "CVC4" in output, "You did not provide correct solver"

        super().__init__(
            executor=executor,
            timeout_secs=timeout_secs,
            target_metric=target_metric,
            metric_weight=metric_weight,
            base=base,
            solver_name="cvc4",
        )


class Z3StatisticsComparisonPredicate(StatisticsComparisonOracle):
    """return a score of distance of output distribution of Z3"""

    def parse_stats(self, stat_str: str):
        stat_dict: dict = {}
        lines = stat_str.strip().split("\n")
        for line in lines[1:]:
            if len(line) <= 1 or line[1] != ":":
                continue  # Skip the line that has no relationship with Z3 stats
            key, value = line.split()
            while key[0] == ":":
                # Z3 stats looks like ":A      123)", so we store key=A and value=123
                key = key[1:]
            if not self.check_in_metric(key):  # For each attribute, check if it's in target metric
                continue
            if value[-1] == ")":
                value = value[:-1]
            stat_dict[key] = float(value) * self.metric_weight.get(key)
        return stat_dict

    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = -1.0,
        target_metric=None,
        metric_weight=None,
        base: SmtLibScript = None,
    ):
        output = executor.run_solver(
            args=["-version"], script=base, timeout_seconds=timeout_secs
        ).stdout
        assert "Z3" in output, "You did not provide correct solver"

        super().__init__(
            executor=executor,
            timeout_secs=timeout_secs,
            target_metric=target_metric,
            metric_weight=metric_weight,
            base=base,
            solver_name="z3",
        )


class ModelPreserveOracle(Oracle):
    def __init__(
        self,
        executor: SolverExecutor,
        timeout_secs: float = 1.0,
        num_trials: int = 5,
        base: SmtLibScript = None,
        solver_name: str = "z3",
    ):
        assert base is not None, "You need to provide the base formula for oracle check"
        assert solver_name in {
            "z3",
            "cvc5",
            "cvc4",
        }, "Do not support the given solver"
        assert IsSatExecutionOracle(executor, timeout_secs, num_trials).check(
            base
        ), "The base formula should be sat"
        self.base = base
        self.sort = False
        get_model_command = SmtLibCommand(name="get-model", args=[])
        if "get-model" not in str(self.base):
            self.base.add_command(get_model_command)
        if solver_name == "z3":
            self.base_output = executor.run_solver(script=base).stdout
        elif solver_name == "cvc5" or solver_name == "cvc4":
            self.base_output = executor.run_solver(script=base, args=["--produce-models"]).stdout
        model = self.base_output[self.base_output.index("(") + 1 : self.base_output.rindex(")")]

        def handle_sort(model_str: str) -> str:
            # Custom-sort is a special case that need to be checked instead of directly copy-and-paste the model
            # We need to add definition to make model able to parse
            with tempfile.NamedTemporaryFile(suffix=".smt2", mode="w+t") as fOut:
                self.base.serialize(fOut, daggify=False)
                fOut.flush()
                fOut.seek(0)
                base_smt2 = fOut.read()

            addition_line = ""
            for line in base_smt2.split("\n"):
                if "declare-sort" in line or "define-sort" in line:  # add sort declare and define
                    addition_line += line + "\n"
            pattern = r"\(define-fun (\w+) \(\) \((.*?)\)\s+(\w+!val!\d+)\)"
            # use pattern to find the temp variable in model
            temp_variable_set = []
            matches = re.findall(pattern, model_str.replace("\n", ""))
            for match in matches:
                if match[2] in temp_variable_set:
                    continue
                temp_variable_set.append(match[2])
                addition_line += (
                    "(declare-const " + match[2] + " (" + match[1] + "))"
                )  # add temp variable declare in model
            return addition_line + model_str

        if "define-sort" in str(self.base):
            model = handle_sort(model)  # handle custom-sort
            self.sort = True
        model_smtlib = StringIO(model)
        self.model_script = SmtLibParser().get_script(model_smtlib)

        def _check_script(formula: SmtLibScript) -> bool:
            limit = sys.getrecursionlimit()
            # Increase the limit of recursion to avoid possible error for deepcopy
            try:
                formula1 = copy.deepcopy(formula)
            except RecursionError as e:
                sys.setrecursionlimit(10 * limit)
                formula1 = copy.deepcopy(formula)
                logging.info(
                    f"The formula is large, so we increase the recursion limit. If {e} happens again, consider"
                    f" reduce the size of the formula"
                )
            # We need to use deepcopy, otherwise it will change the original formula
            sys.setrecursionlimit(limit)
            # Set back to default to avoid possible errors
            for cmd in self.model_script:
                if cmd.name == "define-fun":
                    expr = cmd.args[0]
                    for i, arg in enumerate(formula1):
                        if (arg.name == "declare-fun" or arg.name == "declare-const") and (
                            str(arg.args[0]) == expr
                        ):
                            formula1.commands[i] = cmd
                            break
            if self.sort:
                for cmd in self.model_script:  # Handle sort. Add temp variable declare
                    if cmd.name == "declare-const":
                        expr = cmd.args[0]
                        for i, arg in enumerate(formula1):
                            if (expr == arg.args[-1]) and (arg.name == "define-fun"):
                                formula1.commands.insert(i, cmd)
                                break
            is_sat_oracle = IsSatExecutionOracle(
                executor=executor,
                timeout_secs=timeout_secs,
                num_trials=num_trials,
            )
            return is_sat_oracle(formula1)

        super().__init__(_check_script)

    def get_model(self) -> dict:
        return self.model_script

    def get_base_output(self) -> str:
        return self.base_output
