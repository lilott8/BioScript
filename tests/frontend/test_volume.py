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

		vol = self.get_volume(self, tree, file)

		assert vol[0] == False
		assert sum(vol[1]['a1']['volumes']) == 50