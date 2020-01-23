import pytest

from chemicals.chemtypes import ChemTypes
from compiler.data_structures.symbol_table import SymbolTable
from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.typing
class TestTypingHeader(FrontEndBase):
    def test_manifest_typing_unknown(self, get_visitor):
        file = "test_cases/header/typing_unknown.bs"
        tree = get_visitor(file)
        st = FrontEndBase.run_globals(tree, SymbolTable())

        aaa = st.get_global('aaa')

        assert aaa.types == {ChemTypes.SILOXANES, ChemTypes.UNKNOWN}

    def test_manifest_typing(self, get_visitor):
        file = "test_cases/header/typing_known.bs"
        tree = get_visitor(file)
        st = FrontEndBase.run_globals(tree, SymbolTable())

        aaa = st.get_global('bbb')
        assert aaa.types == {ChemTypes.REDUCING_AGENTS_WEAK, ChemTypes.SALTS_ACIDIC}


@pytest.mark.frontend
@pytest.mark.typing
class TestMix(FrontEndBase):
    pass


@pytest.mark.frontend
@pytest.mark.typing
class TestSplit(FrontEndBase):
    pass