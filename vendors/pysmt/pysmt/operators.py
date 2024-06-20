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
"""This module defines all the operators used internally by pySMT.

Note that other expressions can be built in the FormulaManager, but
they will be rewritten (during construction) in order to only use
these operators.
"""
from itertools import chain


ALL_TYPES = list(range(0,108))

(
FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF, # Boolean Logic (0-6)
SYMBOL, FUNCTION,                           # Symbols and functions calls (7-8)
REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT, STR_CONSTANT, # Constants (9-12)
PLUS, MINUS, TIMES,                         # LIA/LRA operators (13-15)
LE, LT, EQUALS,                             # LIA/LRA relations (16-18)
ITE,                                        # Term-ite (19)
TOREAL,                                     # LIRA toreal() function (20)
#
# MG: FLOOR? INT_MOD_CONGR?
#
# BV
BV_CONSTANT,                                # Bit-Vector constant (21)
BV_NOT, BV_AND, BV_OR, BV_XOR,              # Logical Operators on Bit (22-25)
BV_CONCAT,                                  # BV Concatenation (26)
BV_EXTRACT,                                 # BV sub-vector extraction (27)
BV_ULT, BV_ULE,                             # Unsigned Comparison (28-29)
BV_NEG, BV_ADD, BV_SUB,                     # Basic arithmetic (30-32)
BV_MUL, BV_UDIV, BV_UREM,                   # Division/Multiplication (33-35)
BV_LSHL, BV_LSHR,                           # Shifts (36-37)
BV_ROL, BV_ROR,                             # Rotation (38-39)
BV_ZEXT, BV_SEXT,                           # Extension (40-41)
BV_SLT, BV_SLE,                             # Signed Comparison (42-43)
BV_COMP,                                    # Returns 1_1 if the arguments are
                                            # equal otherwise it returns 0_1 (44)
BV_SDIV, BV_SREM,                           # Signed Division and Reminder(45-46)
BV_ASHR,                                    # Arithmetic shift right (47)
#
# STRINGS
#
STR_LENGTH,                                 # Length (48)
STR_CONCAT,                                 # Concat (49)
STR_CONTAINS,                               # Contains (50)
STR_INDEXOF,                                # IndexOf (51)
STR_REPLACE,                                # Replace (52)
STR_SUBSTR,                                 # Sub String (53)
STR_PREFIXOF,                               # Prefix (54)
STR_SUFFIXOF,                               # Suffix (55)
STR_TO_INT,                                 # atoi (56)
INT_TO_STR,                                 # itoa (57)
STR_CHARAT,                                 # Char at an index (58)
#
# ARRAYS
#
ARRAY_SELECT,                               # Array Select (59)
ARRAY_STORE,                                # Array Store (60)
ARRAY_VALUE,                                # Array Value (61)

DIV,                                        # Arithmetic Division (62)
POW,                                        # Arithmetic Power (63)
ALGEBRAIC_CONSTANT,                         # Algebraic Number (64)
BV_TONATURAL,                               # BV to Natural Conversion (65)
#
# Unicode strings and regexes https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml
#
STR_TO_RE,                                  # String to regex (66)
STR_IN_RE,                                  # String matched by regex (67)
RE_ALL,                                     # \Sigma* (68)
RE_ALLCHAR,                                 # \Sigma, i.e., all strings of length 1 (69)
RE_NONE,                                    # Regex empty language (70)
RE_CONCAT,                                  # Regex concatenation (re.++ RegLan RegLan RegLan :left-assoc) (71)
RE_UNION,                                   # Regex union (re.union RegLan RegLan RegLan :left-assoc) (72)
RE_INTER,                                   # Regex intersection (re.inter RegLan RegLan RegLan :left-assoc) (73)
RE_STAR,                                    # Regex Kleene start (re.* RegLan RegLan) (74)
# Other missing operators from stmlib standard
STR_COMPARE,                                # Compares string (str.<= String String Bool :chainable) (75)
STR_REPLACE_ALL,                            # Replace all instances of a substring (str.replace_all String String String String) (76)
STR_REPLACE_RE,                             # Replaces shortest leftmost match of regex in string (str.replace_re String RegLan String String) (77)
STR_REPLACE_RE_ALL,                         # Replaces all shortest non-empty matches of reges in string (str.replace_re_all String RegLan String String) (78)
RE_COMP,                                    # Regex complement (re.comp RegLan RegLan) (79)
RE_DIFF,                                    # Regex difference   (re.diff RegLan RegLan RegLan :left-assoc) (80)
RE_PLUS,                                    # Regex Kleene cross (re.+ e) abbreviates (re.++ e (re.* e)) (81)
RE_OPT,                                     # Regex optional: (re.opt e) abbreviates (re.union e (str.to_re "")) (82)
RE_RANGE,                                   # Set of all singleton strings s within a range (83)
RE_POWER,                                   # Regex from concatenating a regex n times (84)
RE_LOOP,                                    # Regex from the union of the powers n1 to n2 of a base regex (85)
RNE,                                        # roundNearestTiesToEven RoundingMode (86)
RNA,                                        # roundNearestTiesToAway RoundingMode (87)
RTP,                                        # roundTowardPositive RoundingMode (88)
RTN,                                        # roundTowardNegative RoundingMode (89)
RTZ,                                        # roundTowardZero RoundingMode (90)
REAL_TO_INT,                                # Reals to_int (91)
LET,                                        # Let (92)
FLOOR_DIV,                                  # Integer division: (div Int Int Int) (93)
MOD,                                        # Integer division reminder: (mod Int Int Int) (94)
ABS,                                        # Integer absolute value: (abs Int Int) (95)
GE, GT,                                     # Greater or equal and strictly greater (96, 97)
IS,                                         # Check if term belongs to datatype (98)
BV_TO_INT,                                  # convert bitvector to an int (99) -- z3 specific
INT_TO_BV,                                  # convert int to bitvector (100)
ANNOTATION,                                 # fake operator used to encode annotated nodes (101)
BV_UGT, BV_UGE,                             # comparison operations complementary to BV_ULT, BV_ULE (102-103)
BV_NOR, BV_NAND,                            # bitvector operations nor and nand (104-105)
BV_XNOR, BV_SMOD                            # bitvector xnor and smod (106-107)
) = ALL_TYPES

QUANTIFIERS = frozenset([FORALL, EXISTS])

BOOL_CONNECTIVES = frozenset([AND, OR, NOT, IMPLIES, IFF])

BOOL_OPERATORS = frozenset(QUANTIFIERS | BOOL_CONNECTIVES) | frozenset([LET, ])

ROUNDING_MODES = frozenset([RNE, RNA, RTP, RTN, RTZ])

REGEX_CONSTANTS = frozenset([RE_ALL, RE_ALLCHAR, RE_NONE])

CONSTANTS = frozenset([BOOL_CONSTANT, REAL_CONSTANT, INT_CONSTANT,
                       BV_CONSTANT, STR_CONSTANT, ALGEBRAIC_CONSTANT]) \
                    | REGEX_CONSTANTS | ROUNDING_MODES

# Relations are predicates on theory atoms.
# Relations have boolean type. They are a subset of the operators for a theory
BV_RELATIONS = frozenset([BV_ULE, BV_ULT, BV_UGT, BV_ULE, BV_UGE, BV_SLT, BV_SLE])

IRA_RELATIONS = frozenset([LE, LT, GE, GT])

STR_RELATIONS = frozenset([STR_CONTAINS, STR_PREFIXOF, STR_SUFFIXOF])

RELATIONS = frozenset((EQUALS,)) | BV_RELATIONS | IRA_RELATIONS | STR_RELATIONS

# Operators are functions that return a Theory object
BV_OPERATORS = frozenset([BV_NOT, BV_AND, BV_NAND, BV_OR, BV_NOR, BV_XOR, BV_XNOR,
                          BV_CONCAT, BV_EXTRACT, BV_NEG, BV_ADD,
                          BV_SUB, BV_MUL, BV_UDIV, BV_UREM, BV_LSHL, BV_LSHR,
                          BV_ROL, BV_ROR, BV_ZEXT, BV_SEXT,
                          BV_COMP, BV_SDIV, BV_SREM, BV_SMOD, BV_ASHR])

STR_OPERATORS = frozenset([STR_LENGTH, STR_CONCAT, STR_INDEXOF, STR_REPLACE,
                           STR_SUBSTR, STR_CHARAT, STR_TO_INT, INT_TO_STR,
                           STR_TO_RE, STR_IN_RE, STR_REPLACE_ALL, STR_REPLACE_RE, STR_REPLACE_RE_ALL, STR_COMPARE])

REGEX_OPERATORS = frozenset([RE_CONCAT, RE_INTER, RE_UNION, RE_STAR,
                             RE_COMP, RE_DIFF, RE_PLUS, RE_OPT, RE_RANGE, RE_POWER, RE_LOOP])

IRA_OPERATORS = frozenset([PLUS, MINUS, TIMES, TOREAL, DIV, POW, BV_TONATURAL, BV_TO_INT, INT_TO_BV, REAL_TO_INT, FLOOR_DIV, MOD, ABS])

ARRAY_OPERATORS = frozenset([ARRAY_SELECT, ARRAY_STORE, ARRAY_VALUE])

ADT_OPERATORS = frozenset([IS])

THEORY_OPERATORS = IRA_OPERATORS | BV_OPERATORS | ARRAY_OPERATORS | STR_OPERATORS | REGEX_OPERATORS | ADT_OPERATORS

CUSTOM_NODE_TYPES = []

AUXILIARY_NODE_TYPES = frozenset([ANNOTATION])

assert (BOOL_OPERATORS | THEORY_OPERATORS | RELATIONS | \
        CONSTANTS | frozenset((SYMBOL, FUNCTION, ITE))) | AUXILIARY_NODE_TYPES == frozenset(ALL_TYPES)

assert len(BOOL_OPERATORS & THEORY_OPERATORS) == 0
assert len(BOOL_OPERATORS & RELATIONS) == 0
assert len(BOOL_OPERATORS & CONSTANTS) == 0
assert len(THEORY_OPERATORS & RELATIONS) == 0
assert len(THEORY_OPERATORS & CONSTANTS) == 0
assert len(RELATIONS & CONSTANTS) == 0


def new_node_type(node_id=None, node_str=None):
    """Adds a new node type to the list of custom node types and returns the ID."""
    if node_id is None:
        if len(CUSTOM_NODE_TYPES) == 0:
            node_id = ALL_TYPES[-1] + 1
        else:
            node_id = CUSTOM_NODE_TYPES[-1] + 1

    assert node_id not in ALL_TYPES
    assert node_id not in CUSTOM_NODE_TYPES
    CUSTOM_NODE_TYPES.append(node_id)
    if node_str is None:
        node_str = "Node_%d" % node_id
    __OP_STR__[node_id] = node_str
    return node_id


def op_to_str(node_id):
    """Returns a string representation of the given node."""
    return __OP_STR__[node_id]


def all_types():
    """Returns an iterator over all base and custom types."""
    return chain(iter(ALL_TYPES), iter(CUSTOM_NODE_TYPES))


__OP_STR__ = {
    FORALL : "FORALL",
    EXISTS : "EXISTS",
    AND : "AND",
    OR : "OR",
    NOT : "NOT",
    IMPLIES : "IMPLIES",
    IFF : "IFF",
    SYMBOL : "SYMBOL",
    FUNCTION : "FUNCTION",
    REAL_CONSTANT : "REAL_CONSTANT",
    BOOL_CONSTANT : "BOOL_CONSTANT",
    INT_CONSTANT : "INT_CONSTANT",
    STR_CONSTANT : "STR_CONSTANT",
    PLUS : "PLUS",
    MINUS : "MINUS",
    TIMES : "TIMES",
    LE : "LE",
    LT : "LT",
    EQUALS : "EQUALS",
    ITE : "ITE",
    TOREAL : "TOREAL",
    BV_CONSTANT : "BV_CONSTANT",
    BV_NOT : "BV_NOT",
    BV_AND : "BV_AND",
    BV_NAND : "BV_NAND",
    BV_OR : "BV_OR",
    BV_NOR : "BV_NOR",
    BV_XOR : "BV_XOR",
    BV_XNOR : "BV_XNOR",
    BV_CONCAT : "BV_CONCAT",
    BV_EXTRACT : "BV_EXTRACT",
    BV_ULT : "BV_ULT",
    BV_UGT : "BV_UGT",
    BV_ULE : "BV_ULE",
    BV_UGE : "BV_UGE",
    BV_NEG : "BV_NEG",
    BV_ADD : "BV_ADD",
    BV_SUB : "BV_SUB",
    BV_MUL : "BV_MUL",
    BV_UDIV : "BV_UDIV",
    BV_UREM : "BV_UREM",
    BV_LSHL : "BV_LSHL",
    BV_LSHR : "BV_LSHR",
    BV_ROL : "BV_ROL",
    BV_ROR : "BV_ROR",
    BV_ZEXT : "BV_ZEXT",
    BV_SEXT : "BV_SEXT",
    BV_SLT : "BV_SLT",
    BV_SLE : "BV_SLE",
    BV_COMP : "BV_COMP",
    BV_SDIV : "BV_SDIV",
    BV_SREM : "BV_SREM",
    BV_SMOD : "BV_SMOD",
    BV_ASHR : "BV_ASHR",
    STR_LENGTH: "STR_LENGTH",
    STR_CONCAT: "STR_CONCAT",
    STR_CONTAINS: "STR_CONTAINS",
    STR_INDEXOF: "STR_INDEXOF",
    STR_REPLACE:"STR_REPLACE",
    STR_SUBSTR: "STR_SUBSTR",
    STR_PREFIXOF: "STR_PREFIXOF",
    STR_SUFFIXOF: "STR_SUFFIXOF",
    STR_TO_INT: "STR_TO_INT",
    INT_TO_STR: "INT_TO_STR",
    STR_CHARAT: "STR_CHARAT",
    BV_TONATURAL : "BV_TONATURAL",
    ARRAY_SELECT : "ARRAY_SELECT",
    ARRAY_STORE : "ARRAY_STORE",
    ARRAY_VALUE : "ARRAY_VALUE",
    DIV: "DIV",
    POW: "POW",
    ALGEBRAIC_CONSTANT: "ALGEBRAIC_CONSTANT",
    STR_TO_RE: "STR_TO_RE",
    STR_IN_RE: "STR_IN_RE",
    RE_ALL: "RE_ALL",
    RE_ALLCHAR: "RE_ALLCHAR",
    RE_NONE: "RE_NONE",
    RE_CONCAT: "RE_CONCAT",
    RE_UNION: "RE_UNION",
    RE_INTER: "RE_INTER",
    RE_STAR: "RE_STAR",
    STR_COMPARE: "STR_COMPARE",
    STR_REPLACE_ALL: "STR_REPLACE_ALL",
    STR_REPLACE_RE: "STR_REPLACE_RE",
    STR_REPLACE_RE_ALL: "STR_REPLACE_RE_ALL",
    RE_COMP: "RE_COMP",
    RE_DIFF: "RE_DIFF",
    RE_PLUS: "RE_PLUS",
    RE_OPT: "RE_OPT",
    RE_RANGE: "RE_RANGE",
    RE_POWER: "RE_POWER",
    RE_LOOP: "RE_LOOP",
    RNE: "RNE",
    RNA: "RNA",
    RTP: "RTP",
    RTN: "RTN",
    RTZ: "RTZ",
    REAL_TO_INT: "REAL_TO_INT",
    LET: "LET",
    FLOOR_DIV: "FLOOR_DIV",
    MOD: "MOD",
    ABS: "ABS",
    GE: "GE",
    GT: "GT",
    IS: "IS",
    BV_TO_INT: "BV_TO_INT",
    INT_TO_BV: "INT_TO_BV",
    ANNOTATION: "ANNOTATION"
}
