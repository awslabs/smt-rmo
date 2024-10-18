# SMT Rewriter Modulo Oracles 
This repository contains SMT Rewriter Modulo Oracles (SMT-RMO), a tool for minimizing and obfuscating [SMT](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) formulas.

## Running SMT-RMO

We recommend using [poetry](https://python-poetry.org) for managing your python environment.

### Minimize and obfuscate a segfaulting input
Here we want to minimize and obfuscate an SMTLIB script that causes a version of `z3` to segfault.
```bash
poetry run python src/smt_rmo/cli.py \
    --oracle=segfault \
    --solver=<z3 solver binary path> \
    --minimize --obfuscate \
    <smtlib script path>
```

### Obfuscate while maintaining solver stats
Suppose you have a benchmark that you wish to obfuscate while maintaining its behavior. We define "behavior" using the statistics of an SMT solver, e.g., number of conflicts or memory consumption. In the following example, we will take an SMTLIB script and ask SMT-RMO to obfuscate it while trying to maintain two behaviors of CVC5, `STRINGS_REGISTER_TERM` and `ARITH_UNATE`, which count numbers of different string and arithmetic lemma inferences. We will tolerate a difference of up to 10% in those stats, denoted by `--stats-threshold=0.1`.
```bash
poetry run python src/smt_rmo/cli.py \
    --oracle=stats \
    --stats-threshold=0.1 \
    --track-stat theory::strings::inferencesLemma{STRINGS_REGISTER_TERM} \
    --track-stat theory::arith::inferencesLemma{ARITH_UNATE} \
    --solver=<cvc5 solver path>\
    --obfuscate \
    <smtlib script path>
```
If you execute the above, you will notice that SMT-RMO obfuscates 34 out of 38 constants -- the ones it fails to obfuscate are standard regexes: `[0-9]` and `[a-z]`.
You will also notice that the obfuscated file matches the original on those two stats, `STRINGS_REGISTER_TERM` and `ARITH_UNATE`. 

If you're unsure which stats to track, simply don't supply any and SMT-RMO will use a machine-learned set of stats for the given logic and solver.

*Note: To avoid ambiguity for CVC5 stat names, it is advisable to supply the complete path of a stat, as shown above, instead of just the leaf.*

### Obfuscate while maintaining unsatisfiability
Suppose you have a formula that is unsat and you want to obfuscate it while maintaining equisatisfiablity. This can be done using the `unsat` oracle.
```bash
poetry run python src/smt_rmo/cli.py \
    --oracle=unsat \
    --solver=<cvc4 solver path> \
    --obfuscate \
    <smtlib script path>
```
*Note: for `sat`, you would use `--oracle=sat`.*

### Differential minimization
Consider a script that causes a performance regression between two versions of a solver. Here we have a script that is solved immediately by `cvc4` but that times out with `cvc5`. We can use a differential oracle to minimize/obfuscate the file while maintaining this difference in performance.
```
poetry run python src/smt_rmo/cli.py \
    --oracle=timeout_regression \
    --solver=<cvc4 solver path> \
    --solver2=<cvc5 solver path> \
    --solver-timeout=2 \
    --minimize \
    <smtlib script path>
```

## Oracles

SMT-RMO requires the user to specify an *oracle*, a function that *constrains* how SMT-RMO obfuscates/minimizes an SMTLIB file. For example, the `segfault` oracle ensures that a segfault exhibited by the input file is maintained in the output file. Below we list all the oracles currently provided in SMT-RMO.

| Oracle name      | Description |
| ----------- | ----------- |
| `segfault`      | Maintains segfault in input file       |
| `exitcode`   | Maintains a user provided exit code, provided using `--signal`        |
| `timeout` | Maintains that the file times out within a user-provided bound, provided using `--solver-timeout` |
| `stdout`, `stderr`, `stdouterr` | Maintains that stdout/err matches a given regex, provided using `--regex` |
| `sat`, `unsat`, `unknown` | Maintains that (un)satisfiablity or "unknown" |
| `timeout_regression` | Maintains that `solver` terminates and `solver2` times out, provided using `solver-timeout` |
| `stats` | Maintains that the `solver` (CVC5 or Z3) stats only change by some percentage, provided by `threshold` |  

For debugging purposes, we also provide the `true` and `false` oracles, which accept/reject any SMTLIB script, respectively.

## Upcoming features
- FloatingPoint support
- Fuzzing for generating many benchmarks from a single seed
- Stronger methods for obfuscating constants

## License

This project is licensed under the Apache-2.0 License.
