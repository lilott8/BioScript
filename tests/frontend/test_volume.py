import pytest

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from compiler.data_structures.symbol_table import SymbolTable
from shared.bs_exceptions import UndefinedVariable, UndefinedFunction, UnsupportedOperation
from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.dispense
class TestDispense(FrontEndBase):

    def test_basic(self, get_visitor):
        file = "test_cases/volume/dispense_volume.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0] == False
        assert sum(vol[1]['a1']['volumes']) == 50

    def test_if_else(self, get_visitor):
        file = "test_cases/volume/dispense_if_else.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0] == False

        assert sum(vol[1]['a2']['volumes']) == 10

        for i in range(5):
            assert vol[1]['b1']['volumes'][i] == 2


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.dispose
class TestDispose(FrontEndBase):

    def test_basic(self, get_visitor):
        file = "test_cases/volume/dispose.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0] == False
        assert sum(vol[1]['a1']['volumes']) == -1
