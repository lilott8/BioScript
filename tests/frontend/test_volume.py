import pytest

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from compiler.data_structures.symbol_table import SymbolTable
from shared.bs_exceptions import UndefinedVariable, UndefinedFunction, UnsupportedOperation
from tests.frontend.front_end_base import FrontEndBase

@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.dispose
class TestMix(FrontEndBase):

    def test_basic(self, get_visitor):
        file = "test_cases/volume/mix_basic.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0] == False

        assert sum(vol[1]['a1']['volumes']) == -1
        assert sum(vol[1]['b1']['volumes']) == -1
        assert sum(vol[1]['c1']['volumes']) == 20

    def test_offset(self, get_visitor):
        file = "test_cases/volume/mix_single_offset_use.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0] == False
        assert sum(vol[1]['a1']['volumes']) == -1
        assert sum(vol[1]['a_21']['volumes']) == -1
        assert sum(vol[1]['a_31']['volumes']) == -1
        assert vol[1]['a_s1']['volumes'][0] == -1
        assert vol[1]['a_s1']['volumes'][1] == 10
        assert sum(vol[1]['b1']['volumes']) == -1
        assert sum(vol[1]['c1']['volumes']) == 20


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
