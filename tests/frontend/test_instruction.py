import pytest

from chemicals.identifier import NaiveIdentifier
from compiler.data_structures.symbol_table import SymbolTable
from compiler.data_structures.variable import *
from compiler.semantics.global_visitor import GlobalVariableVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.symbol_visitor_v2 import SymbolTableVisitorV2
from shared.bs_exceptions import UnsupportedOperation


@pytest.mark.frontend
def test_manifests(get_visitor):
    file = "test_cases/header/manifest.bs"
    tree = get_visitor(file)
    st = InstructionBase.run_globals(tree, SymbolTable())

    mod = st.get_global('mod')
    stat = st.get_global('stat')
    mani = st.get_global('aaa')

    assert isinstance(mod, Module)
    assert mod.size == 1
    assert mod.value == 'mod'

    assert isinstance(stat, Stationary)
    assert stat.size == 1
    assert stat.volume['quantity'] == float("inf") and stat.volume['units'] == BSVolume.MICROLITRE

    assert isinstance(mani, Movable)
    assert mani.size == 1
    assert mani.volume['quantity'] == float("inf") and mani.volume['units'] == BSVolume.MICROLITRE


class InstructionBase(metaclass=ABCMeta):

    @staticmethod
    def run_globals(tree, symbol_table: SymbolTable = SymbolTable()) -> SymbolTable:
        global_visitor = GlobalVariableVisitor(symbol_table, NaiveIdentifier())
        global_visitor.visit(tree)
        return global_visitor.symbol_table

    @staticmethod
    def run_methods(tree, symbol_table: SymbolTable) -> SymbolTable:
        method_visitor = MethodVisitor(symbol_table)
        method_visitor.visit(tree)
        return method_visitor.symbol_table

    @staticmethod
    def run_symbols(tree, symbol_table: SymbolTable) -> SymbolTable:
        symbol_visitor = SymbolTableVisitorV2(symbol_table, NaiveIdentifier())
        symbol_visitor.visit(tree)
        return symbol_visitor.symbol_table

    def get_symbols(self, tree):
        st = InstructionBase.run_globals(tree, SymbolTable())
        st = InstructionBase.run_methods(tree, st)
        return InstructionBase.run_symbols(tree, st)


@pytest.mark.frontend
@pytest.mark.instructions
@pytest.mark.dispense
class TestDispense(InstructionBase):

    def test_dispense_simd(self, get_visitor):
        file = "test_cases/dispense/simd_pass.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert isinstance(output, Movable)
        assert output.size == 10
        assert output.volume['quantity'] == 100.00

    def test_dispense_sisd(self, get_visitor):
        file = "test_cases/dispense/sisd_pass.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert isinstance(output, Movable)
        assert output.size == 1
        assert output.volume['quantity'] == 10.0


@pytest.mark.frontend
@pytest.mark.instructions
@pytest.mark.mix
class TestMix(InstructionBase):

    def teardown(self):
        # called after each function
        pass

    def setup(self):
        # Called before at each function
        pass

    def setup_class(self):
        # Called before the class is instantiated.
        pass

    def teardown_class(self):
        # Called as the class is being destroyed
        pass

    def test_simd_equal(self, get_visitor):
        file = "test_cases/mix/simd_pass.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert output.size == 2
        assert output.volume['quantity'] == 40 and output.volume['units'] == BSVolume.MICROLITRE
        assert input_1.volume['quantity'] == 0 and input_1.volume['units'] == BSVolume.MICROLITRE
        assert input_2.volume['quantity'] == 0 and input_2.volume['units'] == BSVolume.MICROLITRE

    def test_mix_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(KeyError):
            file = "test_cases/mix/sisd_index_fail.bs"
            st = self.get_symbols(get_visitor(file))

    def test_mix_sisd_index_in_bounds(self, get_visitor):
        file = "test_cases/mix/sisd_index_pass.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert output.size == 1
        assert output.volume['quantity'] == 20.0 and output.volume['units'] == BSVolume.MICROLITRE
        assert input_1.volume['quantity'] == 10.0 and input_1.size == 2 and input_1.value[1].volume['quantity'] == 0.00
        assert input_2.volume['quantity'] == 10.0 and input_2.size == 2 and input_2.value[0].volume['quantity'] == 0.00

    def test_sisd_no_index(self, get_visitor):
        file = "test_cases/mix/sisd_no_index.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert output.size == 1
        # assert input_1.size == 1 and input_1.volume['quantity'] == 0.00 and \
        #        input_1.volume['units'] == BSVolume.MICROLITRE
        # assert input_2.size == 1 and input_2.volume['quantity'] == 0.00 and \
        #        input_2.volume['units'] == BSVolume.MICROLITRE

    def test_mix_simd_unequal(self, get_visitor):
        with pytest.raises(UnsupportedOperation):
            file = "test_cases/mix/simd_fail.bs"
            st = self.get_symbols(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.instructions
@pytest.mark.split
class TestSplit(object):
    pass
