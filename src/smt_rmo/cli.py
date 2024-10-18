# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import math
from smt_rmo.oracles import (
    InconsistentSatDifferentialOracle,
    SegFaultExecutionOracle,
    TrueOracle,
    OutputRegexExecutionOracle,
    TimeoutExecutionOracle,
    IsSatExecutionOracle,
    IsUnsatExecutionOracle,
    IsUnknownExecutionOracle,
    CheckReturnSignalExecutionOracle,
    TimeoutRegressionDifferentialExecutionOracle,
    CVC4StatisticsComparisonPredicate,
    CVC5StatisticsComparisonPredicate,
    Z3StatisticsComparisonPredicate,
)

import os
import pathlib
from time import perf_counter
import click
import logging
from smt_rmo.ddmin import BFSDDMinTraverser, ddmin_assertions, ddmin_script
from smt_rmo.executors import SolverExecutor
from pysmt.environment import Environment
from pysmt.smtlib.parser import SmtLibParser, SmtLibScript
import pysmt.smtlib.commands as smtcmd
from pysmt.oracles import SizeOracle
from smt_rmo.library import DEFAULT_GREEDY_REWRITERS, DefaultDDMinRewriters
from smt_rmo.obfuscator import (
    IdentifiersObfuscatorWalker,
    Renamer,
    replace_constants,
)
from smt_rmo.strategies import BFSGlobalVisitor
from smt_rmo.tokenizers import RandomTokenizer
from smt_rmo.utils import (
    MultipleTimeoutBudget,
    NodeCollectorWalker,
    TimeoutBudget,
    copy_script_replace_assertions,
    merge_obfuscated,
    track_timeout_budget,
)

logger = logging.getLogger(__name__)


def options_required_for_oracle(require_name, require_map):
    class CommandOptionRequiredClass(click.Command):
        def invoke(self, ctx):
            require = ctx.params[require_name]
            if require not in require_map:
                raise click.ClickException(
                    "Unexpected value for --'{}': {}".format(
                        require_name, require
                    )
                )
            required_suboptions = require_map[require]["required"]

            for required_suboption in required_suboptions:
                if ctx.params[required_suboption.lower()] is None:
                    raise click.ClickException(
                        "With {}={} must specify option --{}".format(
                            require_name, require, required_suboption
                        )
                    )
            super(CommandOptionRequiredClass, self).invoke(ctx)

    return CommandOptionRequiredClass


# dictionary defining required CLI flags per oracle
# used to detect missing flags
required_oracle_options = {
    "true": {"required": [], "optional": [], "forbidden": []},
    "exitcode": {
        "required": ["solver", "signal"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "segfault": {
        "required": ["solver"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "timeout": {
        "required": ["solver", "solver_timeout"],
        "optional": ["retry", "solver-arg"],
        "forbidden": [],
    },
    "timeout_regression": {
        "required": ["solver", "solver2", "solver_timeout"],
        "optional": ["retry", "solver_arg", "solver2_arg"],
        "forbidden": [],
    },
    "inconsistentsat": {
        "required": ["solver", "solver2"],
        "optional": [
            "retry",
            "solver_arg",
            "solver2_arg",
            "solver_timeout",
            "preserve_inconsistency_striclty",
        ],
        "forbidden": [],
    },
    "stdout": {
        "required": ["solver", "regex"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "stderr": {
        "required": ["solver", "regex"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "stdouterr": {
        "required": ["solver", "regex"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "sat": {
        "required": ["solver"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "unsat": {
        "required": ["solver"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "unknwon": {
        "required": ["solver"],
        "optional": ["solver_timeout", "retry", "solver_arg"],
        "forbidden": [],
    },
    "stats": {
        "required": ["solver", "stats_threshold"],
        "optional": ["solver_timeout", "retry", "solver_arg", "track_stat"],
        "forbidden": [],
    },
}


@click.command(
    context_settings=dict(max_content_width=800),
    cls=options_required_for_oracle("oracle", required_oracle_options),
)
@click.argument(
    "input-file",
    required=True,
    type=click.Path(exists=True, dir_okay=False, resolve_path=True),
)
@click.option(
    "--oracle",
    type=click.Choice(
        required_oracle_options.keys(),
        case_sensitive=False,
    ),
    required=True,
    help="Type of oracle. Each oracle may make use of different options among those below",
    multiple=False,
)
@click.option(
    "--solver",
    required=False,
    type=click.Path(exists=False),
    is_eager=True,
    multiple=False,
    help="Path of the solver executable",
)
@click.option(
    "--solver2",
    required=False,
    type=click.Path(exists=False),
    is_eager=True,
    multiple=False,
    help="Path of the second solver executable",
)
@click.option(
    "--signal",
    required=False,
    type=int,
    is_eager=True,
    multiple=False,
    help='The required exitcode for an "exitcode" oracle',
)
@click.option(
    "--stats-threshold",
    required=False,
    type=float,
    multiple=False,
    help="Percentage difference to be tolared by the stats oracle. Must be positive.",
)
@click.option(
    "--track-stat",
    required=False,
    type=str,
    multiple=True,
    default=None,
    help="Solver stat to track for stats oracle. If not provided, RMO uses machine-learned stats.",
)
@click.option(
    "--retry",
    required=False,
    type=int,
    default=None,
    is_eager=True,
    multiple=False,
    help="Maximum number of times the oracle may retry to run the solver (default: 1)",
)
@click.option(
    "--seed",
    required=False,
    type=int,
    default=None,
    is_eager=True,
    multiple=False,
    help="Seed to fix random generators",
)
@click.option(
    "--regex",
    required=False,
    type=str,
    is_eager=True,
    multiple=False,
    help='Regular expression a "stdout" or a "stderr" should look for',
)
@click.option(
    "--solver-timeout",
    required=False,
    type=float,
    default=None,
    is_eager=True,
    multiple=False,
    help="Timeout in seconds allowed for a solver execution (default: -1 = unbounded).",
)
@click.option(
    "--solver-arg",
    required=False,
    type=str,
    is_eager=True,
    multiple=True,
    help="Additional arguments to pass to the solver. One option per argument",
)
@click.option(
    "--solver2-arg",
    required=False,
    type=str,
    is_eager=True,
    multiple=True,
    help="Additional arguments to pass to the second solver. One option per argument",
)
@click.option(
    "--dd-min",
    is_flag=True,
    required=False,
    type=bool,
    multiple=False,
    help="Perform delta minimization",
)
@click.option(
    "--greedy-min",
    is_flag=True,
    required=False,
    type=bool,
    multiple=False,
    help='Perform greedy minimization operations. If used together with "--dd-min", delta minimization will be performed first',
)
@click.option(
    "--minimize",
    is_flag=True,
    required=False,
    type=bool,
    multiple=False,
    help="Perform ddmin and greedymin. Overrides dd-min and greedy-min options.",
)
@click.option(
    "--obfuscate-identifiers",
    is_flag=True,
    required=False,
    type=bool,
    multiple=False,
    help="Obfuscate all identifiers, including function and custom sort names",
)
@click.option(
    "--obfuscate-constants",
    is_flag=True,
    required=False,
    type=bool,
    multiple=False,
    help="Attempt to obfuscate constants",
)
@click.option(
    "--obfuscate",
    is_flag=True,
    required=False,
    type=bool,
    multiple=False,
    help="Attempt to obfuscate constants and identifiers. Overrides --obfuscate-constants and --obfuscate-identifiers.",
)
@click.option(
    "--output-file",
    required=False,
    type=str,
    multiple=False,
    default="",
    help='Output path. If not specified, the output is saved alongside the input with extension ".rmo.smt2"',
)
@click.option(
    "--log",
    type=click.Choice(
        ["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
        case_sensitive=False,
    ),
    default="INFO",
    help="Logging level (default: INFO)",
)
@click.option(
    "--log-file",
    type=click.Path(exists=False),
    required=False,
    help="Log file. Logs are printed to stderr by default",
)
@click.option(
    "--collapse-assertions",
    required=False,
    is_flag=True,
    type=bool,
    multiple=False,
    default=False,
    help="Collapse all the assertions into a single one. If used on incremental problems, it will simplify out all the push/pop commands.",
)
@click.option(
    "--minimize-result-script",
    required=False,
    is_flag=True,
    type=bool,
    multiple=False,
    default=False,
    help="Collapse all the assertions into a single one. If used on incremental problems, it will simplify out all the push/pop commands.",
)
@click.option(
    "--preserve-inconsistency-striclty",
    required=False,
    is_flag=True,
    type=bool,
    multiple=False,
    default=False,
    help="When used with 'inconsistentsat' oracle, it preserves the very same inconsistency of the initial proble, e.g., solver1 must always be sat and solver2 must always be unsat.",
)
@click.option(
    "--timeout",
    required=False,
    is_flag=False,
    type=float,
    multiple=False,
    default=float("inf"),
    help="Set a timeout for the cumulative time spent in minimization and obfuscation (see readme for details)",
)
@click.option(
    "--ddmin-timeout",
    required=False,
    is_flag=False,
    type=float,
    multiple=False,
    default=float("inf"),
    help="Set a timeout for the time spent in delta minimization",
)
@click.option(
    "--greedymin-timeout",
    required=False,
    is_flag=False,
    type=float,
    multiple=False,
    default=float("inf"),
    help="Set a timeout for the time spent in greedy minimization",
)
@click.option(
    "--obfuscation-timeout",
    required=False,
    is_flag=False,
    type=float,
    multiple=False,
    default=float("inf"),
    help="Set a timeout for the time spent in obfuscation",
)
def cli(
    input_file,
    oracle,
    solver,
    solver2,
    signal,
    retry,
    seed,
    regex,
    solver_timeout,
    solver_arg,
    solver2_arg,
    dd_min,
    greedy_min,
    minimize,
    obfuscate_identifiers,
    obfuscate_constants,
    obfuscate,
    output_file,
    log,
    log_file,
    stats_threshold,
    track_stat,
    collapse_assertions,
    minimize_result_script,
    preserve_inconsistency_striclty,
    timeout,
    ddmin_timeout,
    greedymin_timeout,
    obfuscation_timeout,
):
    end_to_end_time_start = perf_counter()

    numeric_level = getattr(logging, log.upper(), None)
    if not isinstance(numeric_level, int):
        raise ValueError("Invalid log level: %s" % log)

    # set defaults
    if retry is None:
        retry = 1
    if solver_timeout is None:
        solver_timeout = -1.0

    # initialize log file
    if log_file:
        logging.basicConfig(
            filename=log_file,
            filemode="w",
            format="%(levelname)s - %(asctime)s: %(message)s",
            level=numeric_level,
        )
    else:
        logging.basicConfig(
            format="%(levelname)s - %(asctime)s: %(message)s",
            level=numeric_level,
        )

    # construct timeouts
    global_timeout_budget = TimeoutBudget(timeout)
    ddmin_timeout_budget = MultipleTimeoutBudget(
        TimeoutBudget(ddmin_timeout), global_timeout_budget
    )
    greedymin_timeout_budget = MultipleTimeoutBudget(
        TimeoutBudget(greedymin_timeout), global_timeout_budget
    )
    obfuscation_timeout_budget = MultipleTimeoutBudget(
        TimeoutBudget(obfuscation_timeout), global_timeout_budget
    )

    # minimize flag forces greedy minimization and ddmin to execute in sequence
    if minimize:
        greedy_min = True
        dd_min = True

    # obfuscate flag forces constant and identifier obfuscation to occur
    if obfuscate:
        obfuscate_constants = True
        obfuscate_identifiers = True

    if dd_min or greedy_min or obfuscate_constants:
        if not oracle:
            print(
                "An oracle must be specified when running with minimization or constant obfuscation options"
            )
            exit(-1)
    else:
        if not obfuscate_identifiers:
            print(
                "At least one task among --dd-min, --greedy-min, --obfuscate-identifiers, and --obfuscate-constants should be enabled."
            )
            exit(-1)

    ###### RMO workflow ######

    try:
        # Parsing
        pysmt_environment: Environment = Environment()

        try:
            with open(str(input_file), "r") as fIn:
                start_time = perf_counter()
                parser = SmtLibParser(environment=pysmt_environment)
                script = parser.get_script(fIn)

        except Exception as e:
            logger.debug(e)
            raise e

        # if collapse assertions is set on incremental problems, emit warning
        if collapse_assertions and any(
            c.name == smtcmd.PUSH or c.name == smtcmd.POP
            for c in script.commands
        ):
            logger.warning(
                "collapse-assertions set for incremental file. This will simplify out all push/pop contexts!"
            )

        # remove set-info commands by default
        script_cmds = list(
            filter(
                lambda x: x.name not in [smtcmd.SET_INFO, smtcmd.ECHO],
                script.commands,
            )
        )

        script = SmtLibScript()
        script.commands = script_cmds
        overall_formula = script.get_last_formula()

        # Create solver(s)
        if solver is not None:
            solver_obj = SolverExecutor(solver, list(solver_arg))

        if solver2 is not None:
            solver2_obj = SolverExecutor(solver2, list(solver2_arg))

        # oracle_obj = None
        if oracle == "true":
            oracle_obj = TrueOracle()

        elif oracle == "exitcode":
            oracle_obj = CheckReturnSignalExecutionOracle(
                solver_obj, int(signal), float(solver_timeout), int(retry)
            )

        elif oracle == "segfault":
            oracle_obj = SegFaultExecutionOracle(
                solver_obj, float(solver_timeout), int(retry)
            )

        elif oracle == "timeout":
            oracle_obj = TimeoutExecutionOracle(
                solver_obj, float(solver_timeout), int(retry)
            )

        elif oracle == "timeout_regression":
            oracle_obj = TimeoutRegressionDifferentialExecutionOracle(
                solver_obj,
                solver2_obj,
                float(solver_timeout),
                float(solver_timeout),
                int(retry),
                int(retry),
            )
        elif oracle == "inconsistentsat":
            oracle_obj = InconsistentSatDifferentialOracle(
                solver_obj,
                solver2_obj,
                float(solver_timeout),
                float(solver_timeout),
                int(retry),
                int(retry),
                preserve_inconsistency_striclty,
            )
        elif oracle in ["stdout", "stderr", "stdouterr"]:
            search_stdout = oracle in ["stdout", "stdouterr"]
            search_stderr = oracle in ["stderr", "stdouterr"]
            oracle_obj = OutputRegexExecutionOracle(
                solver_obj,
                regex,
                search_stdout,
                search_stderr,
                float(solver_timeout),
                int(retry),
            )

        elif oracle == "sat":
            oracle_obj = IsSatExecutionOracle(
                solver_obj, float(solver_timeout), int(retry)
            )

        elif oracle == "unsat":
            oracle_obj = IsUnsatExecutionOracle(
                solver_obj, float(solver_timeout), int(retry)
            )

        elif oracle == "unknown":
            oracle_obj = IsUnknownExecutionOracle(
                solver_obj, float(solver_timeout), int(retry)
            )
        elif oracle == "stats":
            assert stats_threshold >= 0, "Threshold must be >= 0."
            if not track_stat:
                track_stat = None
                logging.log(
                    logging.INFO,
                    "No stats provided to track. Using RMO's default stats for given logic",
                )
            # check which solver we're using to initialize appropriate oracle
            output = solver_obj.run_solver(
                args=["--version"],
                script=script,
                timeout_seconds=float(solver_timeout),
            ).stdout
            if "This is cvc5 version" in output:
                for stat in track_stat:
                    if "::" not in stat:
                        logging.log(
                            logging.WARN,
                            f"For {stat}, if you don't give the head for the stat attributes, then it may be "
                            "ambiguous \n For example, resource::steps::inference-id{STRINGS_EXTF} and "
                            "theory::strings::inferencesLemma{STRINGS_EXTF}. It might affect the result.",
                        )
                oracle_obj = CVC5StatisticsComparisonPredicate(
                    executor=solver_obj,
                    timeout_secs=float(solver_timeout),
                    target_metric=track_stat,
                    base=script,
                )
            elif "This is CVC4 version" in output:
                oracle_obj = CVC4StatisticsComparisonPredicate(
                    executor=solver_obj,
                    timeout_secs=float(solver_timeout),
                    target_metric=track_stat,
                    base=script,
                )
            elif "Z3 version" in output:
                oracle_obj = Z3StatisticsComparisonPredicate(
                    executor=solver_obj,
                    timeout_secs=float(solver_timeout),
                    target_metric=track_stat,
                    base=script,
                )
            else:
                raise Exception(
                    "Cannot identify which solver is being invoked. Cannot instantiate SolverStatistics predicate"
                )
            oracle_obj = oracle_obj.soft_predicate_to_oracle(
                lower_bound=0, upper_bound=stats_threshold
            )

        assert (
            oracle_obj is not None
        ), f"Could not instantiate an oracle object for option {oracle}"

        # wrapper function to execute oracle on assertion maps
        def oracle_fun(a2f):
            return oracle_obj(copy_script_replace_assertions(script, a2f))

        # build original to obfuscated assertions map
        if collapse_assertions:
            assertion_to_formula = {-1: overall_formula}
        else:
            assertion_to_formula = {
                i: cmd.args[0]
                for i, cmd in enumerate(script.commands)
                if cmd.name == smtcmd.ASSERT
            }

        if not oracle_fun(assertion_to_formula):
            logger.info("The input file does not satisfy the oracle. Aborting.")
            print("The input file does not satisfy the oracle. Aborting.")
            exit(0)

        if dd_min or greedy_min:
            # Utility function to collect stats on problem size reduction

            def problem_size(a2f):
                PYSMT_SIZE_ORACLE = SizeOracle()
                return sum(
                    PYSMT_SIZE_ORACLE.get_size(a)
                    for a in a2f.values()
                    if a is not None
                )

        if dd_min:
            if not collapse_assertions:
                logging.log(
                    logging.INFO,
                    "Applying DDMIN algorithm on the list of assertions",
                )
                start_time = perf_counter()
                # ddmin pass at assertions level to remove unnecessary assertions first
                assertion_to_formula = ddmin_assertions(
                    assertion_to_formula,
                    oracle_fun,
                    timeout_budget=ddmin_timeout_budget,
                )

            logging.log(
                logging.INFO,
                f"Applying DDMIN algorithm {'' if collapse_assertions else 'on each assertion'}",
            )
            try:
                start_time = perf_counter()

                for c, f in assertion_to_formula.items():
                    if f is None:
                        continue
                    ddMinimizer = BFSDDMinTraverser(
                        DefaultDDMinRewriters(
                            assertion_to_formula,
                            c,
                            oracle_fun,
                            pysmt_environment,
                        ),
                        pysmt_environment,
                    )
                    assertion_to_formula[c] = ddMinimizer.visit(
                        assertion_to_formula[c]
                    )
                    
                    ## intermediate assert for debugging:
                    # assert oracle_fun(
                    #     assertion_to_formula
                    # ) 

                if not ddmin_timeout_budget.available():
                    logger.info("DDMin timed out")

            except Exception as e:
                logger.debug(e)
                raise e

        if greedy_min:
            logging.log(logging.INFO, "Applying GreedyMin algorithm")
            try:
                start_time = perf_counter()

                for c, f in assertion_to_formula.items():
                    if not greedymin_timeout_budget.available():
                        break  # shortcut

                    if f is None:
                        continue

                    def per_assertion_oracle(formula):
                        tmp_a2f = dict(assertion_to_formula)
                        tmp_a2f[c] = formula
                        return oracle_fun(tmp_a2f)

                    greedy_visitor = BFSGlobalVisitor(
                        DEFAULT_GREEDY_REWRITERS(per_assertion_oracle),
                        lambda x: True,
                        pysmt_environment,
                        timeout_budget=greedymin_timeout_budget,
                    )
                    assertion_to_formula[c] = greedy_visitor.visit(
                        assertion_to_formula[c]
                    )
                    
                    ## intermediate assertion for debugging
                    # assert oracle_fun(
                    #     assertion_to_formula
                    # )

                if not greedymin_timeout_budget.available():
                    logger.info("GredyMin timed out")

            except Exception as e:
                logger.debug(e)
                raise e

        # Create random tockenizer
        tokenizer = RandomTokenizer(seed=seed)

        if obfuscate_constants:
            logging.log(logging.INFO, "Obfuscating constants")
            try:
                start_time = perf_counter()
                (
                    int_constants,
                    string_constants,
                    real_constants,
                    char_constants,
                    bv_constants,
                ) = (
                    set(),
                    set(),
                    set(),
                    set(),
                    set(),
                )

                # Collect constants
                for c, f in assertion_to_formula.items():
                    if f is None:
                        continue

                    int_constants |= NodeCollectorWalker(
                        lambda node, args: node.is_int_constant()
                    ).walk(f)
                    string_constants |= NodeCollectorWalker(
                        lambda node, args: node.is_string_constant()
                    ).walk(f)
                    real_constants |= NodeCollectorWalker(
                        lambda node, args: node.is_real_constant()
                    ).walk(f)

                    char_constants |= NodeCollectorWalker(
                        lambda node, args: node.is_string_constant()
                        and node.str_unary_hex(),
                        skip_subtree=lambda node, args: node.is_re_const(),
                    ).walk(f)

                    bv_constants |= NodeCollectorWalker(
                        lambda node, args: node.is_bv_constant()
                    ).walk(f)

                # Initialize random generators
                def random_int_generator(formula, target_constant):
                    return pysmt_environment.formula_manager.Int(
                        tokenizer.random_int()
                    )

                def random_real_generator(formula, target_constant):
                    num = tokenizer.random_int()
                    return pysmt_environment.formula_manager.Real(float(num))

                def random_string_generator(formula, target_constant):
                    return pysmt_environment.formula_manager.String(
                        tokenizer.random_string()
                    )

                def random_char_generator(formula, target_constant):
                    return pysmt_environment.formula_manager.String(
                        tokenizer.random_hex_character(), unary_hex=True
                    )

                def random_bv_generator(formula, target_constant):
                    width = target_constant.bv_width()
                    return pysmt_environment.formula_manager.BV(
                        tokenizer.random_bv(width), width=width
                    )

                constant_to_generator_map = {
                    k: v
                    for d in (
                        {ci: random_int_generator for ci in int_constants},
                        {cr: random_real_generator for cr in real_constants},
                        {
                            cs: random_string_generator
                            for cs in string_constants
                        },
                        {cb: random_bv_generator for cb in bv_constants},
                        {cc: random_char_generator for cc in char_constants},
                    )
                    for k, v in d.items()
                }
                MAX_ATTEMPTS = 10

                failed_to_replace = set()

                for c, f in assertion_to_formula.items():
                    if f is None:
                        continue

                    def per_assertion_oracle(formula):
                        tmp_a2f = dict(assertion_to_formula)
                        tmp_a2f[c] = formula
                        return oracle_fun(tmp_a2f)

                    (
                        assertion_to_formula[c],
                        failed_to_replace_f,
                    ) = replace_constants(
                        f,
                        constant_to_generator_map,
                        per_assertion_oracle,
                        environment=pysmt_environment,
                        max_attempts=MAX_ATTEMPTS,
                        timeout_budget=obfuscation_timeout_budget,
                    )

                    failed_to_replace |= failed_to_replace_f

                if not obfuscation_timeout_budget.available():
                    logger.info("Constant obfuscation timed out")

                if failed_to_replace:
                    logging.log(
                        logging.INFO,
                        f"failed to replace {len(failed_to_replace)} out of {len(constant_to_generator_map)}{' (remained in the file after minimization)' if dd_min or greedy_min else ''}: {failed_to_replace}",
                    )
                else:
                    logging.log(logging.INFO, "All constants replaced.")

            except Exception as e:
                logger.debug(e)
                raise e

        if obfuscate_identifiers:
            logging.log(logging.INFO, "Obfuscating identifiers")
            num_types_to_obfuscate, num_symbols_to_obfuscate = None, None
            num_types_obfuscated, num_symbols_obfuscated = None, None
            type_names_failed_to_replace, symbol_names_failed_to_replace = (
                set(),
                set(),
            )
            try:
                start_time = perf_counter()

                # collect all symbols
                all_symbols = NodeCollectorWalker(
                    lambda node, args: node.is_symbol()
                ).walk(overall_formula)
                # retrieve how many custom sorts have been defined in the original file ()
                num_custom_sorts = max(
                    len(pysmt_environment.type_manager._custom_types),
                    len(pysmt_environment.type_manager._custom_types_decl),
                )

                identifiers_len = (
                    # assume as worst case that each symbol has a different custom type
                    math.ceil(
                        math.log2(len(all_symbols) + num_custom_sorts + 1) + 1
                    )
                )

                # saving a copy of the formula before obfuscation to enable rollback in case
                # the global obfuscation pass fails
                assertion_to_formula_bkp = dict(assertion_to_formula)

                renamer = Renamer(identifiers_length=identifiers_len)

                # first, try to rename all symbols. We always attempt this step, regardless of timeouts, because it is critical and fast
                for c, f in assertion_to_formula.items():
                    if f is None:
                        continue

                    assertion_to_formula[c] = IdentifiersObfuscatorWalker(
                        renamer, env=pysmt_environment
                    ).walk(assertion_to_formula[c])

                num_types_to_obfuscate, num_symbols_to_obfuscate = (
                    len(renamer._type_replacements),
                    len(renamer._symbol_replacements),
                )

                # defining oracle adapter for obfuscated script
                def obf_oracle_function(a2f):
                    return oracle_obj(merge_obfuscated(script, a2f, {**renamer._type_replacements, **renamer._symbol_replacements}))

                if obf_oracle_function(assertion_to_formula):
                    num_types_obfuscated, num_symbols_obfuscated = (
                        num_types_to_obfuscate,
                        num_symbols_to_obfuscate,
                    )
                    replaced_names_mapping = {
                        **renamer._type_replacements,
                        **renamer._symbol_replacements,
                    }

                else:
                    # could not obfuscate all identifiers. Trying to obfuscate one by one, starting with types.
                    # here we consider the timeout budget

                    # roll back to initial formula
                    assertion_to_formula = assertion_to_formula_bkp

                    start_time = perf_counter()
                    type_names = renamer._type_replacements.keys()
                    last_valid_candidate_formula = dict(assertion_to_formula)
                    type_names_replaced = set()
                    replaced_names_mapping = {}

                    # rename types
                    for type_name in type_names:
                        if not obfuscation_timeout_budget.available():
                            break  # shortcut

                        with track_timeout_budget(obfuscation_timeout_budget):
                            renamer_types = Renamer(
                                identifiers_length=identifiers_len,
                                allow_list_types=set([type_name]),
                                allow_list_symbols=set(),
                            )

                            for c, f in assertion_to_formula.items():
                                if f is None:
                                    continue

                                assertion_to_formula[
                                    c
                                ] = IdentifiersObfuscatorWalker(
                                    renamer_types, env=pysmt_environment
                                ).walk(
                                    assertion_to_formula[c]
                                )

                            def obf_oracle_function(a2f):
                                return oracle_obj(merge_obfuscated(script, a2f, {**replaced_names_mapping, **renamer_types._type_replacements}, type_names_failed_to_replace))

                            if obf_oracle_function(assertion_to_formula):
                                last_valid_candidate_formula = dict(
                                    assertion_to_formula
                                )
                                replaced_names_mapping.update(
                                    renamer_types._type_replacements
                                )
                                type_names_replaced.add(type_name)
                            else:
                                assertion_to_formula = dict(
                                    last_valid_candidate_formula
                                )

                    type_names_failed_to_replace = (
                        set(type_names) - type_names_replaced
                    )

                    # rename symbols
                    symbol_names_replaced = set()
                    symbol_names = renamer._symbol_replacements.keys()
                    last_valid_candidate_formula = dict(assertion_to_formula)

                    for symbol_name in symbol_names:
                        if not obfuscation_timeout_budget.available():
                            break  # shortcut

                        with track_timeout_budget(obfuscation_timeout_budget):
                            renamer_symbols = Renamer(
                                identifiers_length=identifiers_len,
                                allow_list_types=set(),
                                allow_list_symbols=set([symbol_name]),
                            )

                            for c, f in assertion_to_formula.items():
                                if f is None:
                                    continue

                                assertion_to_formula[
                                    c
                                ] = IdentifiersObfuscatorWalker(
                                    renamer_symbols, env=pysmt_environment
                                ).walk(
                                    assertion_to_formula[c]
                                )

                            def obf_oracle_function(a2f):
                                return oracle_obj(merge_obfuscated(script, a2f, {**replaced_names_mapping, **renamer_symbols._symbol_replacements}, symbol_names_replaced | type_names_failed_to_replace))

                            if obf_oracle_function(assertion_to_formula):
                                last_valid_candidate_formula = dict(
                                    assertion_to_formula
                                )
                                replaced_names_mapping.update(
                                    renamer_symbols._symbol_replacements
                                )
                                symbol_names_replaced.add(symbol_name)
                            else:
                                assertion_to_formula = dict(
                                    last_valid_candidate_formula
                                )

                    symbol_names_failed_to_replace = (
                        set(symbol_names) - symbol_names_replaced
                    )

                    num_types_obfuscated = num_types_to_obfuscate - len(
                        type_names_failed_to_replace
                    )
                    num_symbols_obfuscated = num_symbols_to_obfuscate - len(
                        symbol_names_failed_to_replace
                    )

                logger.info(
                    f"Successfully obfuscated {num_types_obfuscated} out of {num_types_to_obfuscate} custom sorts{' (remained in the file after minimization)' if dd_min or greedy_min else ''}"
                )
                logger.info(
                    f"Successfully obfuscated {num_symbols_obfuscated} out of {num_symbols_to_obfuscate} symbol identifiers{' (remained in the file after minimization)' if dd_min or greedy_min else ''}"
                )

            except Exception as e:
                logger.debug(e)
                raise e

            # create result script after obfuscation
            result_script = merge_obfuscated(
                script, assertion_to_formula, replaced_names_mapping
            )
        else:
            # No obfuscation
            result_script = copy_script_replace_assertions(
                script, assertion_to_formula
            )

        if minimize_result_script:
            try:
                # applying a final round of ddmin across all the commands in the result file to remove
                # any unnecessary command, including options settings or unnecessary push-pop contexts
                start_time = perf_counter()
                num_commands_before_ddmin_script = len(result_script.commands)
                logger.info("DDMinimizing the result script")
                result_script = ddmin_script(
                    result_script,
                    oracle_obj,
                    timeout_budget=ddmin_timeout_budget,
                )
                num_commands_after_ddmin_script = len(result_script.commands)
                if (
                    num_commands_after_ddmin_script
                    < num_commands_before_ddmin_script
                ):
                    logger.info(
                        f"DDMin of result script {'completed' if ddmin_timeout_budget.available() else 'timed out'}. {num_commands_before_ddmin_script - num_commands_after_ddmin_script} commands removed"
                    )
            except Exception as e:
                logger.debug(e)
                raise e

        # save output
        if output_file:
            out_filename = pathlib.Path(output_file)
        else:
            out_filename = str(input_file)
            out_filename = (
                out_filename[
                    : out_filename.rfind(".")
                    if "." in out_filename
                    else len(out_filename)
                ]
                + ".rmo"
                + ".smt2"
            )

        with open(out_filename, "wt") as fOut:
            result_script.serialize(fOut, daggify=False)

        logging.log(
            logging.INFO,
            f"Completed in {perf_counter() - end_to_end_time_start} s",
        )

        logging.log(logging.INFO, f"Result saved in: {out_filename}")

        print("\n\nResults\n=======")
        input_file_size = os.path.getsize(input_file)
        output_file_size = os.path.getsize(out_filename)
        size_reduction = (
            1 - float(output_file_size) / float(input_file_size)
        ) * 100
        print(
            f"Size of original file: {input_file_size} bytes",
        )
        print(
            f"Size of output file: {output_file_size} bytes",
        )
        print(f"Size reduction {size_reduction:.1f}%")
        if obfuscate_constants:
            print(
                f"Constants replaced: {len(constant_to_generator_map) - len(failed_to_replace)} out of {len(constant_to_generator_map)}{' (remained in the file after minimization)' if dd_min or greedy_min else ''}"
            )
        if obfuscate_identifiers:
            if num_types_to_obfuscate is None or num_types_obfuscated is None:
                print("Failed to obfuscate custom sorts")
            else:
                print(
                    f"Custom sorts obfuscated: {num_types_obfuscated} out of {num_types_to_obfuscate}{' (remained in the file after minimization)' if dd_min or greedy_min else ''}"
                )
                if type_names_failed_to_replace:
                    print(
                        f"\tfailed to obfuscate the sorts: {type_names_failed_to_replace}"
                    )

            if (
                num_symbols_to_obfuscate is None
                or num_symbols_obfuscated is None
            ):
                print("Failed to obfuscate symbol identifiers")
            else:
                print(
                    f"Symbol identifiers obfuscated: {num_symbols_obfuscated} out of {num_symbols_to_obfuscate}{' (remained in the file after minimization)' if dd_min or greedy_min else ''}"
                )
                if symbol_names_failed_to_replace:
                    print(
                        f"\tFailed to obfuscate the symbols: {symbol_names_failed_to_replace}"
                    )

        print(f"\nResult saved in: {out_filename}")

    except Exception as e:
        logger.exception(e)
        print(
            "\nAn error occurred during the execution of RMO. Please report it.\n"
        )
        print(
            "\nif possible, re-execute with `--log=DEBUG --log-file=forbugreport.txt`"
        )
        print("and attach the log file to your ticket, including the input file if it can be shared. Thanks!")


if __name__ == "__main__":
    cli()
