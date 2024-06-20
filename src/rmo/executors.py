from __future__ import annotations

import os
import shutil
import subprocess
from functools import lru_cache
from pathlib import Path
from tempfile import NamedTemporaryFile
from time import perf_counter
from typing import Any, Dict, List, Tuple, Union

from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.smtlib.parser.parser import SmtLibScript
from pysmt.smtlib.script import smtlibscript_from_formula


class SolverOutput:
    # avoiding a dataclass here to allow use of older python versions
    reserved_keywords = {"return_code", "stdout", "stderr", "execution_time"}

    def __init__(
        self,
        return_code: int,
        stdout: str,
        stderr: str,
        execution_time: float,
        **kwArgs,
    ) -> None:
        self.return_code: int = return_code
        self.stdout: str = stdout
        self.stderr: str = stderr
        self.execution_time: float = execution_time

        assert kwArgs.keys().isdisjoint(
            SolverOutput.reserved_keywords
        ), f"The following keywords are reserved: {SolverOutput.reserved_keywords}"
        self._additional_metrics = dict(kwArgs)

    def __getattribute__(self, name) -> Any:
        try:
            return object.__getattribute__(self, name)
        except AttributeError as e:
            try:
                return self._additional_metrics[name]
            except:
                raise e

    def __repr__(self) -> str:
        res_dict = dict(self._additional_metrics)
        res_dict["return_code"] = self.return_code
        res_dict["stdout"] = self.stdout
        res_dict["stderr"] = self.stderr
        res_dict["execution_time"] = self.execution_time
        return f"SolverOutput[{res_dict}]"

    def __str__(self) -> str:
        return self.__repr__()


def _run_solver(
    solver_bin: Union[str, Path],
    script: Union[SmtLibScript, FNode, str],
    args: List[str] = [],
    timeout_seconds: float = -1.0,
    envvars: Dict[str, str] = None,
    daggify: bool = False,
    pysmt_environment: Environment = Environment(),
) -> SolverOutput:
    assert solver_bin is not None
    assert isinstance(args, List) and all(isinstance(a, str) for a in args)
    assert isinstance(timeout_seconds, float) or isinstance(timeout_seconds, int)
    assert isinstance(script, SmtLibScript) or isinstance(script, FNode) or isinstance(script, str)

    timeout_seconds = float(timeout_seconds)

    if envvars is not None:
        env = os.environ.copy()
        for k, v in envvars.items():
            env[k] = v
        envvars = env

    script = (
        script
        if isinstance(script, SmtLibScript)
        else (
            smtlibscript_from_formula(script, environment=pysmt_environment)
            if isinstance(script, FNode)
            else str(script)
        )
    )

    executable_path = Path(solver_bin).resolve()
    if not executable_path.exists():
        # try to retrive executable from current environment
        executable_in_path = shutil.which(solver_bin)
        if executable_in_path:
            executable_path = Path(executable_in_path).resolve()

    with NamedTemporaryFile(prefix="rmo", suffix=".smt2", mode="wt") as temp_file:
        if isinstance(script, str):
            temp_file.write(script)
        else:
            assert isinstance(script, SmtLibScript)
            script.serialize(temp_file, daggify=daggify)

        temp_file.flush()

        timeout = (
            timeout_seconds if timeout_seconds >= 0 else 7 * 24 * 60 * 60
        )  # 7 days (=infinity) by default

        try:
            start_time = perf_counter()
            result = subprocess.run(
                [str(executable_path)] + args + [temp_file.name],
                timeout=timeout,
                check=False,
                capture_output=True,
                text=True,
                env=envvars,
            )
            return SolverOutput(
                result.returncode,
                result.stdout.strip(),
                result.stderr.strip(),
                perf_counter() - start_time,
            )
        except subprocess.TimeoutExpired as e:
            return None


class SolverExecutor:
    def __init__(
        self,
        solver_bin: Union[str, Path],
        basic_args: List[str] = [],
        envvars: Dict[str, str] = None,
        daggify: bool = False,
        pysmt_environment: Environment = Environment(),
    ) -> None:
        self._solver_bin: Union[str, Path] = solver_bin
        self._basic_args: List[str] = list(basic_args)
        self._envvars: Dict[str, str] = envvars
        self._pysmt_environment: Environment = pysmt_environment
        self._daggify: bool = daggify

    def run_solver(
        self,
        script: Union[SmtLibScript, FNode, str],
        args: List[str] = [],
        timeout_seconds: float = -1.0,
    ) -> SolverOutput:
        all_args = self._basic_args + args
        return _run_solver(
            self._solver_bin,
            script,
            all_args,
            timeout_seconds,
            self._envvars,
            self._daggify,
            self._pysmt_environment,
        )


class CachedSolverExecutor:
    def __init__(self, solver_bin: Union[str, Path], basic_args: List[str] = []) -> None:
        self._solver_bin: Union[str, Path] = solver_bin
        self._basic_args: List[str] = basic_args

    @lru_cache
    def _run_solver_cached(
        self,
        script: Union[SmtLibScript, FNode, str],
        args: Tuple[str] = [],
        timeout_seconds: float = -1.0,
    ) -> SolverOutput:
        all_args = list(self._basic_args) + list(args)
        return _run_solver(self._solver_bin, script, all_args, timeout_seconds)

    def run_solver(
        self,
        script: Union[SmtLibScript, FNode, str],
        args: List[str] = [],
        timeout_seconds: float = -1.0,
    ) -> SolverOutput:
        return self._run_solver_cached(script, tuple(args), timeout_seconds)
