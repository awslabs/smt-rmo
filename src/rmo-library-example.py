# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from io import StringIO
import sys
from contextlib import contextmanager
from pathlib import Path
from time import perf_counter
from pysmt.oracles import SizeOracle
from pysmt.environment import Environment
from pysmt.smtlib.parser import SmtLibParser
import pysmt.smtlib.commands as smtcmd
from smt_rmo.executors import SolverExecutor
from smt_rmo.library import DefaultDDMinRewriters
from smt_rmo.oracles import SegFaultExecutionOracle
from smt_rmo.obfuscator import (
    IdentifiersObfuscatorWalker,
    Renamer,
    replace_constants,
)
from smt_rmo.rewriters import AnyRewriter, LambdaRewriter
from smt_rmo.ddmin import BFSDDMinTraverser, ddmin_script
from smt_rmo.strategies import BFSGlobalVisitor
from smt_rmo.tokenizers import RandomTokenizer
from smt_rmo.utils import (
    NodeCollectorWalker,
    copy_script_replace_assertions,
    merge_obfuscated,
)


##################### INPUT and OUTPUT paths ####################

INPUT_FILE = (
    Path.cwd()
    / "benchmarks"
    / "dafny-Source-IntegrationTests-bin-Debug-net6.0-TestFiles-LitTests-LitTest-dafny1-BinaryTree.dfy.15.smt2"
)

OUTPUT_DEMO = Path.cwd() / "demo.smt2"

assert INPUT_FILE.exists()


################### Utilities for demonstration ##################
INITIAL_INPUT_SIZE = 1  # Will be set after parsing
PYSMT_SIZE_ORACLE = SizeOracle()


@contextmanager
def monitor_time(name: str) -> float:
    global script, assertion_to_formula, INITIAL_INPUT_SIZE

    print(f"{name}...", end="", flush=True)
    # capture stdout
    stdout = sys.stdout
    sys.stdout = tmp_stdout = StringIO()

    start = perf_counter()
    yield
    step_duration = perf_counter() - start

    sys.stdout = stdout
    print(f" completed in {step_duration:.4f} secs")
    captured_output = tmp_stdout.getvalue().replace("\n", "\n\t")
    if captured_output:
        print("\t" + captured_output)

    tmp_script = copy_script_replace_assertions(script, assertion_to_formula)

    current_size = float(
        PYSMT_SIZE_ORACLE.get_size(tmp_script.get_last_formula())
    )
    relative_size = current_size / INITIAL_INPUT_SIZE
    print(f"\trelative input size: {relative_size*100 :.2f}%\n")


def log_message(message):
    # print(message)
    pass


def pause():
    # input()
    pass


############## Executor and oracle specifications ###############

solver = SolverExecutor("solvers/z3-4.12.1-Linux")
segfault_oracle = SegFaultExecutionOracle(
    solver, timeout_secs=2.0, num_trials=1
)
# segfault_oracle = TrueOracle()


################# Standard configurations ######################

environment: Environment = Environment()

################# Parsing ######################

with open(str(INPUT_FILE), "r") as fIn:
    parser = SmtLibParser(environment=environment)
    script = parser.get_script(fIn)

COLLAPSE_ASSERTIONS = True

overall_formula = script.get_last_formula()
INITIAL_INPUT_SIZE = float(PYSMT_SIZE_ORACLE.get_size(overall_formula))
print(f"Initial input size (number of parse tree nodes): {INITIAL_INPUT_SIZE}")

# Minimize the script to remove unnecessary commands
if not COLLAPSE_ASSERTIONS:
    with monitor_time("Script commands delta minimization"):
        script = ddmin_script(script, segfault_oracle)
        assertion_to_formula = {
            i: cmd.args[0]
            for i, cmd in enumerate(script.commands)
            if cmd.name == smtcmd.ASSERT
        }
else:
    assertion_to_formula = {-1: overall_formula}


# updating the oracle to include additional serialization options
def oracle(a2f):
    return segfault_oracle(copy_script_replace_assertions(script, a2f))
assert oracle(
    assertion_to_formula
), "The input formula does not satisfy the oracle"


################# Delta minimization ######################

with monitor_time("Delta minimization"):
    for c, f in assertion_to_formula.items():
        ddMinimizer = BFSDDMinTraverser(
            DefaultDDMinRewriters(assertion_to_formula, c, oracle, environment),
            environment,
        )
        assertion_to_formula[c] = ddMinimizer.visit(assertion_to_formula[c])
        assert oracle(assertion_to_formula)

print("Happy!")
################# Greedy replacement examples ######################

with monitor_time("Greedy replacements"):
    for c, f in assertion_to_formula.items():

        def per_assertion_oracle(formula):
            tmp_a2f = dict(assertion_to_formula)
            tmp_a2f[c] = formula
            return oracle(tmp_a2f)

        replace_bool_expr_with_true = (
            LambdaRewriter(lambda expr, args, env: env.formula_manager.TRUE())
            .guarded(
                lambda expr, args, env: expr.get_type()
                == env.type_manager.BOOL()
            )
            .checked(per_assertion_oracle)
        )

        replace_bool_expr_with_false = (
            LambdaRewriter(lambda expr, args, env: env.formula_manager.FALSE())
            .guarded(
                lambda expr, args, env: expr.get_type()
                == env.type_manager.BOOL()
            )
            .checked(per_assertion_oracle)
        )

        replace_int_expr_with_0 = (
            LambdaRewriter(lambda expr, args, env: env.formula_manager.Int(0))
            .guarded(
                lambda expr, args, env: expr.get_type()
                == env.type_manager.INT()
            )
            .checked(per_assertion_oracle)
        )

        replace_int_expr_with_1 = (
            LambdaRewriter(lambda expr, args, env: env.formula_manager.Int(1))
            .guarded(
                lambda expr, args, env: expr.get_type()
                == env.type_manager.INT()
            )
            .checked(per_assertion_oracle)
        )

        greedy_rewriters = AnyRewriter(
            replace_bool_expr_with_true,
            replace_bool_expr_with_false,
            replace_int_expr_with_0,
            replace_int_expr_with_1,
        )

        greedy_visitor = BFSGlobalVisitor(
            greedy_rewriters, lambda x: True, environment
        )
        assertion_to_formula[c] = greedy_visitor.visit(assertion_to_formula[c])
        assert oracle(assertion_to_formula)

print("Very happy!")

################ Constants obfuscation (example) ##########################

with monitor_time("Constants obfuscation"):
    tokenizer = RandomTokenizer()

    int_constants, string_constants = set(), set()
    for c, f in assertion_to_formula.items():
        int_constants |= NodeCollectorWalker(
            lambda node, args: node.is_int_constant()
        ).walk(f)
        string_constants |= NodeCollectorWalker(
            lambda node, args: node.is_string_constant()
        ).walk(f)

    def random_int_generator(formula, target_constant):
        return environment.formula_manager.Int(tokenizer.random_int())

    def random_string_generator(formula, target_constant):
        return environment.formula_manager.String(tokenizer.random_string())

    constant_to_generator_map = {
        k: v
        for d in (
            {ci: random_int_generator for ci in int_constants},
            {cs: random_string_generator for cs in string_constants},
        )
        for k, v in d.items()
    }
    MAX_ATTEMPTS = 10

    failed_to_replace = set()

    for c, f in assertion_to_formula.items():

        def per_assertion_oracle(formula):
            tmp_a2f = dict(assertion_to_formula)
            tmp_a2f[c] = formula
            return oracle(tmp_a2f)

        assertion_to_formula[c], failed_to_replace_f = replace_constants(
            f,
            constant_to_generator_map,
            per_assertion_oracle,
            environment=environment,
            max_attempts=MAX_ATTEMPTS,
        )

        failed_to_replace |= failed_to_replace_f

    if failed_to_replace:
        print(
            f"failed to replace {len(failed_to_replace)} out of {len(constant_to_generator_map)}: {failed_to_replace}"
        )
    else:
        print(f"All {len(constant_to_generator_map)} constants replaced.")


# print("Very very happy!")

################# Identifiers obfuscation and output ######################

with monitor_time("Identifiers obfuscation"):
    # collect all symbols
    import math

    all_symbols = NodeCollectorWalker(lambda node, args: node.is_symbol()).walk(
        overall_formula
    )
    # pysmt_environment.type_mamanger
    identifiers_len = (
        # assume as worst case that each symbol has a different custom type
        math.ceil(math.log2(len(all_symbols) + 1) + 1)
    )
    renamer = Renamer(identifiers_length=3)
    for c, f in assertion_to_formula.items():
        assertion_to_formula[c] = IdentifiersObfuscatorWalker(
            renamer, env=environment
        ).walk(assertion_to_formula[c])


with open(OUTPUT_DEMO, "wt") as fOut:
    # result = copy_script_replace_assertions(script, assertion_to_formula)
    result_script = merge_obfuscated(
        script,
        assertion_to_formula,
        {**renamer._type_replacements, **renamer._symbol_replacements},
    )
    result_script.serialize(fOut, daggify=False)
    assert segfault_oracle(result_script), "obfuscated script fails oracle"

print("Happily done!")
