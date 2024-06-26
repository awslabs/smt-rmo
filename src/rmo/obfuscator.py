# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from typing import Callable, Dict, Set

from pysmt.environment import Environment, get_env
from pysmt.fnode import FNode
from pysmt.typing import PySMTType, TypeManager
from pysmt.walkers import IdentityDagWalker

from rmo.utils import InfiniteTimeoutBudget, TimeoutBudget, track_timeout_budget

from .tokenizers import RandomTokenizer, Tokenizer


class Renamer:
    def __init__(
        self,
        tokenizer: Tokenizer = RandomTokenizer(),
        identifiers_length: int = 10,
        prefix: str = "obf_",
        allow_list_types: Set[str] = None,
        allow_list_symbols: Set[str] = None,
    ) -> None:
        self._tokenizer: Tokenizer = tokenizer
        self._identifiers_length: int = identifiers_length
        self._prefix: str = prefix
        self._identifiers_already_used = set()
        self._symbol_replacements = {}
        self._type_replacements = {}
        self._allow_list_types = allow_list_types
        self._allow_list_symbols = allow_list_symbols

    def _random_tocken(self):
        res = self._tokenizer.random_identifier(length=self._identifiers_length)
        while res in self._identifiers_already_used:
            res = self._tokenizer.random_identifier(length=self._identifiers_length)
        self._identifiers_already_used.add(res)
        return "obf_" + res

    def rename_type(self, name: str) -> str:
        if self._allow_list_types is not None and name not in self._allow_list_types:
            return name

        if name not in self._type_replacements:
            self._type_replacements[name] = self._random_tocken()
        return self._type_replacements[name]

    def rename_symbol(self, name: str) -> str:
        if self._allow_list_symbols is not None and name not in self._allow_list_symbols:
            return name

        if name not in self._symbol_replacements:
            self._symbol_replacements[name] = self._random_tocken()
        return self._symbol_replacements[name]


class IdentifiersObfuscatorWalker(IdentityDagWalker):
    def __init__(self, renamer: Renamer, env=Environment(), invalidate_memoization=None):
        super().__init__(env, invalidate_memoization)
        self._renamer: Renamer = renamer
        self._type_manager: TypeManager = env.type_manager
        self._type_map = {}

    def walk(self, formula, **kwargs):
        return super().walk(formula, **kwargs)

    def _obfuscate_type(self, type_: PySMTType) -> PySMTType:
        """Recursively recreate the given type within the manager and
        obfuscate the name of custom types.

        This proceeds iteratively on the structure of the type tree.
        Adapted from TypeChecker.normalize
        """
        if type_ not in self._type_map:
            stack = [type_]
            while stack:
                ty = stack.pop()

                if (
                    ty.arity == 0
                    and not ty.is_custom_parameterized()
                    and not ty.is_custom_type()
                    and not ty.is_adt_type()
                ):
                    if (
                        ty.is_bool_type()
                        or ty.is_int_type()
                        or ty.is_real_type()
                        or ty.is_string_type()
                        or ty.is_regex_type()
                        or ty.is_rounding_mode_type()
                    ):
                        myty = ty
                    elif ty.is_bv_type():
                        myty = self._type_manager.BVType(ty.width)
                    else:
                        myty = self._type_manager.Type(
                            self._renamer.rename_type(ty.basename), arity=0
                        )
                    self._type_map[ty] = myty
                else:
                    missing = []
                    if ty.is_custom_parameterized():
                        if ty.base_type not in self._type_map:
                            missing.append(ty.base_type)
                        missing += [p for p in ty.parameters if p not in self._type_map]
                    elif ty.is_adt_type():
                        if ty not in self._type_map:
                            # add placeholder to support recursively defined data structures
                            self._type_map[ty] = self._type_manager.ADT(
                                self._renamer.rename_type(ty.name), None
                            )
                        for constructor, selectors in ty.cs:
                            param_types = [s[1] for s in selectors]
                            missing += [
                                pt for pt in param_types if (pt not in self._type_map and pt != ty)
                            ]
                    else:
                        missing += [subtype for subtype in ty.args if subtype not in self._type_map]
                        if ty.is_function_type():
                            if ty.return_type not in self._type_map:
                                missing.append(ty.return_type)

                    if missing:
                        # At least one type still needs to be converted
                        stack.append(ty)
                        stack += missing
                    else:
                        if ty.is_array_type():
                            index_type = self._type_map[ty.index_type]
                            elem_type = self._type_map[ty.elem_type]
                            myty = self._type_manager.ArrayType(index_type, elem_type)
                        elif ty.is_function_type():
                            param_types = (self._type_map[a] for a in ty.param_types)
                            return_type = self._type_map[ty.return_type]
                            myty = self._type_manager.FunctionType(return_type, param_types)
                        elif ty.is_custom_parameterized():
                            myty = self._type_manager.ParameterizedType(
                                self._type_map[ty.base_type],
                                [self._type_map[p] for p in ty.parameters],
                            )
                        elif ty.is_adt_type():
                            assert ty in self._type_map
                            myty = self._type_map[ty]
                            normalized_cs = [
                                (
                                    self._renamer.rename_symbol(c),
                                    [
                                        (
                                            self._renamer.rename_symbol(p[0]),
                                            self._type_map[p[1]],
                                        )
                                        for p in ss
                                    ],
                                )
                                for c, ss in ty.cs
                            ]
                            myty.cs = normalized_cs
                            # temporarily copy reference to old functions. They will have to be normalized
                            # by the formula manager, e.g., in the FormulaContextualizer walker
                            myty.aux_functions = ty.aux_functions
                        else:
                            # Custom Type
                            typedecl = self._type_manager.Type(
                                self._renamer.rename_type(ty.basename), ty.arity
                            )
                            new_args = tuple(self._type_map[a] for a in ty.args) if ty.args else []
                            myty = self._type_manager.get_type_instance(typedecl, *new_args)
                        self._type_map[ty] = myty

        return self._type_map[type_]

    def _obfuscate_symbol(self, name: str) -> str:
        return self._renamer.rename_symbol(name)

    def walk_symbol(self, formula, args, **kwargs):
        return self.mgr.Symbol(
            self._obfuscate_symbol(formula.symbol_name()),
            self._obfuscate_type(formula.symbol_type()),
        )


def replace_constant(
    formula: FNode,
    target_constant: FNode,
    generator: Callable[[FNode, FNode], FNode],
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
    max_attempts: int = 5,
    timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
):
    assert max_attempts > 0
    for _ in range(max_attempts):
        if not timeout_budget.available():
            break

        with track_timeout_budget(timeout_budget):
            replacement_constant = generator(formula, target_constant)
            while replacement_constant == target_constant:
                replacement_constant = generator(formula, target_constant)

            candidate = environment.substituter.substitute(
                formula, {target_constant: replacement_constant}, None
            )
            if oracle(candidate):
                return candidate, replacement_constant

    return formula, None


def replace_constants(
    formula: FNode,
    target_to_generator_map: Dict[FNode, Callable[[FNode, FNode], FNode]],
    oracle: Callable[[FNode], bool],
    environment: Environment = get_env(),
    max_attempts: int = 5,
    timeout_budget: TimeoutBudget = InfiniteTimeoutBudget,
):
    formula = environment.formula_manager.normalize(formula)
    failed_to_replace = set()
    for constant, generator in target_to_generator_map.items():
        formula, replacement = replace_constant(
            formula,
            constant,
            generator,
            oracle,
            environment=environment,
            max_attempts=max_attempts,
            timeout_budget=timeout_budget,
        )
        if replacement is None:
            failed_to_replace.add(constant)
    return formula, failed_to_replace
