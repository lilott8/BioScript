import pytest

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from compiler.data_structures.symbol_table import SymbolTable
from shared.bs_exceptions import UndefinedVariable, UndefinedFunction, UnsupportedOperation
from tests.frontend.front_end_base import FrontEndBase


class TestTypingHeader(FrontEndBase):
    pass


class TestMix(FrontEndBase):
    pass


class TestSplit(FrontEndBase):
    pass