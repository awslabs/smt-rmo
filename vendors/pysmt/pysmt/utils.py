from __future__ import annotations
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
import collections
import re
import itertools


def all_assignments(bool_variables, env):
    """Generates all possible assignments for a set of boolean variables."""
    mgr = env.formula_manager
    for set_ in powerset(bool_variables):
        yield dict((v, mgr.Bool(v in set_)) for v in bool_variables)


def powerset(elements):
    """Generates the powerset of the given elements set.

    E.g., powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    """
    return itertools.chain.from_iterable(itertools.combinations(elements, r)
                                         for r in range(len(elements)+1))

#
# Bit Operations
#
def set_bit(v, index, x):
    """Set the index:th bit of v to x, and return the new value."""
    mask = 1 << index
    if x:
        v |= mask
    else:
        v &= ~mask
    return v


def twos_complement(val, bits):
    """Retuns the 2-complemented value of val assuming bits word width"""
    if (val & (1 << (bits - 1))) != 0: # if sign bit is set
        val = val - (2 ** bits)        # compute negative value
    return val


#
# Python Compatibility Functions
#

def interactive_char_iterator(handle):
    c = handle.read(1)
    while c:
        yield c
        c = handle.read(1)


#
# Symbol (un)quoting
#
_simple_symbol_prog = re.compile(r"^[~!@\$%\^&\*_\-+=<>\.\?\/A-Za-z][~!@\$%\^&\*_\-+=<>\.\?\/A-Za-z0-9]*$")
_simple_numeric = re.compile(r"^\d+?(\.\d+?)?$")
_keywords = set(["Int", "Real", "Bool"])

def quote(name, style='|'):
    if (name in _keywords or _simple_symbol_prog.match(name) is None or ' ' in name) and (len(name) > 1 and name[0] != '|') and (_simple_numeric.match(name) is None):
        name = name.replace("\\", "\\\\").replace("%s" % style, "\\%s" % style)
        return "%s%s%s" % (style, name, style)
    else:
        return name


class ImmutableAnnotations(collections.abc.Mapping):
    
    def __init__(self, keys:tuple=tuple(), values:tuple=tuple()):
        assert isinstance(keys, tuple) and isinstance(values, tuple)
        assert all(isinstance(v, tuple) for v in values)
        assert len(keys) == len(values)

        for k in keys:
            hash(k) # ensures all keys are themselves hashable
        for v in values:
            hash(v) # ensures all values are themselves hashable

        self.__keys = keys # tuple of keys
        self.__values = values # tuple of tuples: each key is associated with a tuple of values
        self.__hash = None


    def add(self, key, value) -> ImmutableAnnotations:
        assert key is not None and value is not None
        hash(key)
        hash(value)
        if self.__contains__(key):
            index = self.__key_to_index(key)
            res_keys, res_values = [], []
            for i in range(len(self.__keys)):
                res_keys.append(self.__keys[i])
                if i == index:
                    new_val = list(self.__values[i])
                    new_val.append(value)
                    res_values.append(tuple(new_val))
                else:
                    res_values.append(self.__values[i])
        else:
            res_keys, res_values = list(self.__keys), list(self.__values)
            res_keys.append(key)
            res_values.append((value, ))
        
        return ImmutableAnnotations(tuple(res_keys), tuple(res_values))

    def removeKey(self, key) -> ImmutableAnnotations:
        assert key is not None
        if key in self.__keys:
            index = self.__key_to_index(key)
            res_keys, res_values = [], []
            for i in range(len(self.__keys)):
                if i != index:
                    res_keys.append(self.__keys[i])
                    res_values.append(self.__values[i])
            return ImmutableAnnotations(tuple(res_keys), tuple(res_values))
        
        return self
                    
    def removeValue(self, key, value) -> ImmutableAnnotations:
        assert key is not None and value is not None
        if key in self.__keys:
            index = self.__key_to_index(key)
            res_keys, res_values = [], []
            value_removed = False
            for i in range(len(self.__keys)):
                if i != index:
                    res_keys.append(self.__keys[i])
                    res_values.append(self.__values[i])
                else:
                    new_values = [v for v in self.__values[i] if v != value]
                    value_removed = len(new_values) < self.__values[i]
                    if not value_removed:
                        # avoid creating a new object if no value was actually removed
                        return self
                    
                    if new_values:
                        res_keys.append(self.__keys[i])
                        res_values.append(tuple(new_values))

            return ImmutableAnnotations(tuple(res_keys), tuple(res_values))
        
        return self

    def replaceValue(self, key, oldValue, newValue) -> ImmutableAnnotations:
        assert key is not None and oldValue is not None
        if newValue is None:
            return self.removeValue(key, oldValue)

        if oldValue == newValue:
            return self

        if key in self.__keys:
            index = self.__key_to_index(key)
            res_keys, res_values = [], []
            value_replaced = False
            for i in range(len(self.__keys)):
                if i != index:
                    res_keys.append(self.__keys[i])
                    res_values.append(self.__values[i])
                else:
                    new_values = []
                    for v in self.__values[i]:
                        if v == oldValue:
                            value_replaced = True
                            new_values.append(newValue)
                        else:
                            new_values.append(v)
                    
                    if not value_replaced:
                        return self
                    
                    res_keys.append(self.__keys[i])
                    res_values.append(tuple(new_values))

            return ImmutableAnnotations(tuple(res_keys), tuple(res_values))
        
        return self


    def __key_to_index(self, key):
        for i, k in enumerate(self.__keys):
            if k == key:
                return i
        raise KeyError(key)

    def __getitem__(self, key):
        index = self.__key_to_index(key)
        return self.__values[index]

    def __contains__(self, key):
        return key in self.__keys

    def __iter__(self):
        return iter(self.__keys)

    def __len__(self):
        return len(self.__keys)

    def as_dict(self):
        d = dict()
        for i in range(len(self.__keys)):
            d[self.__keys[i]] = self.__values[i]
        return d

    def __repr__(self):
        return str(self.as_dict())

    def __str__(self) -> str:
        return self.__repr__()
    
    def __eq__(self, other: object) -> bool:
        if isinstance(other, ImmutableAnnotations):
            return self.__keys == other.__keys and self.__values == other.__values
        return False

    def __hash__(self):
        # lazy computation
        if self.__hash is None:
            h = 0
            for i in range(len(self.__keys)):
                h ^= hash((self.__keys[i], self.__values[i]))
            self.__hash = h
        return self.__hash
