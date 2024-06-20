# PySMT fork
This is a fork of PySMT (https://github.com/pysmt/pysmt) which is under the Apache 2.0 license.
This fork is only meant to be used as part of the Rewriting Modulo Oracles project.

The fork started with PySMT commit a9e4c7117cb78dbbad1372085880f4f7c3232412 in branch master.
We modified the following files.
```bash
README.md
README.rst
pysmt/fnode.py
pysmt/formula.py
pysmt/logics.py
pysmt/operators.py
pysmt/oracles.py
pysmt/parsing.py
pysmt/printers.py
pysmt/shortcuts.py
pysmt/simplifier.py
pysmt/smtlib/annotations.py
pysmt/smtlib/commands.py
pysmt/smtlib/parser/parser.py
pysmt/smtlib/printers.py
pysmt/smtlib/script.py
pysmt/smtlib/solver.py
pysmt/smtlib/utils.py
pysmt/substituter.py
pysmt/test/examples.py
pysmt/test/smtlib/test_annotations.py
pysmt/test/smtlib/test_fuzzed.py
pysmt/test/smtlib/test_parser_examples.py
pysmt/test/smtlib/test_smtlibscript.py
pysmt/test/test_formula.py
pysmt/test/test_logics.py
pysmt/test/test_printing.py
pysmt/type_checker.py
pysmt/typing.py
pysmt/utils.py
pysmt/walkers/dag.py
pysmt/walkers/generic.py
pysmt/walkers/identitydag.py
```

# Current limitations
### ADT
- No support for `match` and parametric ADTs

### let/quantified vars
- Variable names are fresh, losing syntactic equivalence

### floating point
- not supported, except `RoundingMode` type

### recursive functions
- not supported


### CVC4 compatibility
- cvc4 uses non-standard syntax for some operations, where underscore is used instead of dot, e.g., `str.to.int`, `str.to.re` which have been standardized into `str.to_int` and `str.to_re`, respectively. CVC5 instead follows the standard. Similarly, `int.to.str` used by cvc4 has been later standardized into `str.from_int`. We can parse all these variations, but we will print only the standard forms. For example, any instance of `str.to.int` in the input file will be replaced by `str.to_int` in the output file.