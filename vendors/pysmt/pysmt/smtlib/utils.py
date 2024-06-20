#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#

from pysmt.simplifier import Simplifier


class SmtLibModelValidationSimplifier(Simplifier):
    """This class is useful to validate SmtLib models produced by
    `(get-model)` and parsed by `SmtLibParser.parse_model()`.

    This works just like a normal Simplifier, but treats specially the
    symbols starting with @ that are used in SmtLib models to
    represent unique objects (i.e. @XXX is equal to @YYY iff XXX == YYY).

    For example:
    ```
    parser = SmtLibParser(env)
    simplifier = SmtLibModelValidationSimplifier(env)
    formula = parser.get_script(buffer).get_last_formula()
    model, interpretations = parser.parse_model(model_buffer)
    simp = simplifier.simplify(formula.substitute(model, interpretations))
    assert simp == TRUE()
    ```
    """

    def walk_equals(self, formula, args, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        if sl.is_constant() and sr.is_constant():
            l = sl.constant_value()
            r = sr.constant_value()
            return self.manager.Bool(l == r)
        elif sl == sr:
            return self.manager.TRUE()
        elif (
            sl.is_symbol()
            and sr.is_symbol()
            and sl.symbol_name().startswith("@")
            and sr.symbol_name().startswith("@")
        ):
            return self.manager.Bool(sl == sr)
        else:
            return self.manager.Equals(sl, sr)


class UnionFind:
    def __init__(self) -> None:
        self.parent_node = {}
        self.rank = {}
        self.components = None

    def add(self, u):
        if u in self.parent_node:
            return
        self.parent_node[u] = u
        self.rank[u] = 0

    def find(self, k):
        if self.parent_node[k] != k:
            self.parent_node[k] = self.find(self.parent_node[k])
        return self.parent_node[k]

    def union(self, a, b):
        self.add(a)
        self.add(b)

        x = self.find(a)
        y = self.find(b)

        if x == y:
            return
        # invalidate components cache, if any
        self.components = None
        if self.rank[x] > self.rank[y]:
            self.parent_node[y] = x
        elif self.rank[x] < self.rank[y]:
            self.parent_node[x] = y
        else:
            self.parent_node[x] = y
            self.rank[y] = self.rank[y] + 1

    def get_components(self):
        # TODO: can be optimized
        if not self.components:
            self.components = {}
            for element in self.parent_node.keys():
                index = self.find(element)
                self.components[index] = self.components.get(index, set())
                self.components[index].add(element)
        return self.components.values()

    def component(self, a):
        if a not in self.parent_node:
            return None
        self.get_components()
        return self.components[self.find(a)]
