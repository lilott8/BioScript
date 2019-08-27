import pytest

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from compiler.data_structures.symbol_table import SymbolTable
from shared.bs_exceptions import UndefinedVariable, UndefinedFunction, UnsupportedOperation
from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.symbol_table
class TestHeader(FrontEndBase):

    def test_manifests(self, get_visitor):
        file = "test_cases/header/manifest.bs"
        tree = get_visitor(file)
        st = FrontEndBase.run_globals(tree, SymbolTable())

        mod = st.get_global('mod')
        stat = st.get_global('stat')
        mani = st.get_global('aaa')

        assert ChemTypes.MODULE in mod.types and len(mod.types) == 1
        assert ChemTypeResolver.is_mat_in_set(stat.types)
        assert ChemTypeResolver.is_mat_in_set(mani.types)


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.dispense
class TestDispense(FrontEndBase):

    def test_undefined_manifest(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/dispense/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))

            output = st.get_local('a', 'main')

    def test_defined_manifest(self, get_visitor):
        file = "test_cases/dispense/symbol_table_defined.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_mat_in_set(output.types)
        assert output.scope == 'main'


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.mix
class TestMix(FrontEndBase):

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

    def test_mix_with_global(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/mix/symbol_table_mat_global.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.

    def test_mix_mat_with_nat(self, get_visitor):
        file = "test_cases/mix/symbol_table_mat_nat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert ChemTypeResolver.is_only_material(input_1.types)
        assert ChemTypeResolver.is_number_in_set(input_2.types) and ChemTypeResolver.is_number_in_set(input_2.types)
        assert ChemTypeResolver.is_number_in_set(output.types) and ChemTypeResolver.is_mat_in_set(output.types)
        assert input_1.scope == 'main'
        assert input_2.scope == 'main'
        assert output.scope == 'main'

    def test_mix_two_mats(self, get_visitor):
        file = "test_cases/mix/symbol_table_two_mats.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert ChemTypeResolver.is_only_material(input_1.types)
        assert ChemTypeResolver.is_only_material(input_2.types)
        assert ChemTypeResolver.is_only_material(output.types)
        assert input_1.scope == 'main'
        assert input_2.scope == 'main'
        assert output.scope == 'main'

    def test_mix_one_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/mix/symbol_table_mat_global.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.detect
class TestDetect(FrontEndBase):

    def test_mat(self, get_visitor):
        file = "test_cases/detect/symbol_table_mat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        mod = st.get_global('mod')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_only_material(input_1.types)
        assert ChemTypes.MODULE in mod.types and len(mod.types) == 1
        assert not ChemTypeResolver.is_mat_in_set(output.types) and ChemTypeResolver.is_number_in_set(output.types)

    def test_nat(self, get_visitor):
        file = "test_cases/detect/symbol_table_nat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        mod = st.get_global('mod')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_mat_in_set(input_1.types) and ChemTypeResolver.is_number_in_set(input_1.types)
        assert ChemTypes.MODULE in mod.types and len(mod.types) == 1
        assert ChemTypeResolver.is_number_in_set(output.types)

    def test_not_mod(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/detect/symbol_table_not_mod.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.

    def test_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/detect/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.heat
class TestHeat(FrontEndBase):

    def test_mat(self, get_visitor):
        file = "test_cases/heat/symbol_table_mat.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')
        assert ChemTypeResolver.is_only_material(output.types)

    def test_nat(self, get_visitor):
        file = "test_cases/heat/symbol_table_nat.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')
        assert ChemTypeResolver.is_number_in_set(output.types) and ChemTypeResolver.is_mat_in_set(output.types)

    def test_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/heat/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.dispose
class TestDispose(FrontEndBase):

    def test_mat(self, get_visitor):
        file = "test_cases/dispose/symbol_table_mat.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_only_material(output.types)

    def test_nat(self, get_visitor):
        file = "test_cases/dispose/symbol_table_nat.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_number_in_set(output.types) and ChemTypeResolver.is_mat_in_set(output.types)

    def test_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/dispose/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
class TestStore(FrontEndBase):

    def test_mat(self, get_visitor):
        file = "test_cases/store/symbol_table_mat.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_only_material(output.types)

    def test_nat(self, get_visitor):
        file = "test_cases/store/symbol_table_nat.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_number_in_set(output.types) and ChemTypeResolver.is_mat_in_set(output.types)

    def test_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/store/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.split
class TestSplit(FrontEndBase):

    def test_global(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/split/symbol_table_global.bs"
            st = self.get_symbols(get_visitor(file))

    def test_mat(self, get_visitor):
        file = "test_cases/split/symbol_table_mat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_mat_in_set(input_1.types)
        assert ChemTypeResolver.is_only_material(output.types)
        assert input_1.scope == 'main'
        assert output.scope == 'main'

    def test_nat(self, get_visitor):
        file = "test_cases/split/symbol_table_nat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_number_in_set(input_1.types)
        assert ChemTypeResolver.is_number_in_set(output.types) and ChemTypeResolver.is_mat_in_set(output.types)
        assert input_1.scope == 'main'
        assert output.scope == 'main'

    def test_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/split/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.math
class TestMath(FrontEndBase):

    def test_literals(self, get_visitor):
        file = "test_cases/math/symbol_table_literals.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_only_numeric(output.types)

    def test_mat_nat(self, get_visitor):
        file = "test_cases/math/symbol_table_mat_nat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_number_in_set(input_1.types) and ChemTypeResolver.is_number_in_set(input_1.types)
        assert ChemTypeResolver.is_only_numeric(output.types)

    def test_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/math/symbol_table_undefined.bs"
            st = self.get_symbols(get_visitor(file))
            # Testing that an exception is thrown is the test.

    def test_var_literals(self, get_visitor):
        file = "test_cases/math/symbol_table_var_literal.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_only_numeric(output.types)

    def test_numeric_assignment(self, get_visitor):
        file = "test_cases/math/symbol_table_numeric_assignment.bs"
        st = self.get_symbols(get_visitor(file))

        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_only_numeric(output.types)



@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.functions
class TestFunction(FrontEndBase):

    def test_return_mat(self, get_visitor):
        file = "test_cases/function/symbol_table_ret_mat.bs"
        st = self.get_symbols(get_visitor(file))

        ret_val = st.get_local('a', 'foo')
        output = st.get_local('a', 'main')
        func = st.functions['foo']

        assert ChemTypeResolver.is_only_material(ret_val.types)
        assert ChemTypeResolver.is_only_material(output.types)
        assert ChemTypeResolver.is_only_material(func.types)

    def test_return_nat(self, get_visitor):
        file = "test_cases/function/symbol_table_ret_nat.bs"
        st = self.get_symbols(get_visitor(file))

        ret_val = st.get_local('a', 'foo')
        output = st.get_local('a', 'main')
        func = st.functions['foo']

        assert ChemTypeResolver.is_only_numeric(ret_val.types)
        assert ChemTypeResolver.is_only_numeric(output.types)
        assert ChemTypeResolver.is_only_numeric(func.types)

    def test_mat_args(self, get_visitor):
        file = "test_cases/function/symbol_table_mat_args.bs"
        st = self.get_symbols(get_visitor(file))

        arg1 = st.get_local(st.functions['foo'].args[0], 'foo')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_only_material(arg1.types)
        assert ChemTypeResolver.is_only_material(output.types)

    def test_mixed_args(self, get_visitor):
        file = "test_cases/function/symbol_table_mixed_args.bs"
        st = self.get_symbols(get_visitor(file))

        arg1 = st.get_local(st.functions['foo'].args[0], 'foo')
        arg2 = st.get_local(st.functions['foo'].args[1], 'foo')
        output = st.get_local('b', 'main')

        assert ChemTypeResolver.is_only_material(arg1.types)
        assert ChemTypeResolver.is_only_numeric(arg2.types)
        assert ChemTypeResolver.is_only_numeric(output.types)

    def test_nat_args(self, get_visitor):
        file = "test_cases/function/symbol_table_nat_args.bs"
        st = self.get_symbols(get_visitor(file))

        arg1 = st.get_local(st.functions['foo'].args[0], 'foo')
        arg2 = st.get_local(st.functions['foo'].args[1], 'foo')
        output = st.get_local('a', 'main')

        assert ChemTypeResolver.is_only_numeric(arg1.types)
        assert ChemTypeResolver.is_only_numeric(arg2.types)
        assert ChemTypeResolver.is_only_numeric(output.types)
        assert st.get_symbol('CONST_2') is not None

    def test_ret_method(self, get_visitor):
        file = "test_cases/function/symbol_table_ret_method.bs"
        st = self.get_symbols(get_visitor(file))

        assert ChemTypeResolver.is_only_material(st.functions['foo'].types)

    def test_undefined_arg(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/function/symbol_table_undefined_arg.bs"
            st = self.get_symbols(get_visitor(file))

    def test_undefined_function(self, get_visitor):
        with pytest.raises(UndefinedFunction):
            file = "test_cases/function/symbol_table_undefined_function.bs"
            st = self.get_symbols(get_visitor(file))

    def test_no_args_for_expected_args(self, get_visitor):
        with pytest.raises(UnsupportedOperation):
            file = "test_cases/function/symbol_table_send_no_args.bs"
            st = self.get_symbols(get_visitor(file))

    def test_unexpected_args_for_no_args(self, get_visitor):
        with pytest.raises(UnsupportedOperation):
            file = "test_cases/function/symbol_table_send_args.bs"
            st = self.get_symbols(get_visitor(file))

    def test_redeclare_function(self, get_visitor):
        with pytest.raises(UndefinedFunction):
            file = "test_cases/function/symbol_table_redeclare.bs"
            st = self.get_symbols(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.symbol_table
@pytest.mark.instructions
@pytest.mark.gradient
class TestGradient(FrontEndBase):

    def test_two_mats(self, get_visitor):
        file = "test_cases/gradient/symbol_table_two_mats.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert ChemTypeResolver.is_only_material(input_1.types)
        assert ChemTypeResolver.is_only_material(input_2.types)
        assert ChemTypeResolver.is_only_material(output.types)

    def test_invalid_range(self, get_visitor):
        with pytest.raises(UnsupportedOperation):
            file = "test_cases/gradient/symbol_table_invalid_range.bs"
            st = self.get_symbols(get_visitor(file))

    def test_invalid_gradient(self, get_visitor):
        with pytest.raises(UnsupportedOperation):
            file = "test_cases/gradient/symbol_table_invalid_gradient.bs"
            st = self.get_symbols(get_visitor(file))

    def test_mat_global(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/gradient/symbol_table_mat_global.bs"
            st = self.get_symbols(get_visitor(file))

    def test_mat_nat(self, get_visitor):
        file = "test_cases/gradient/symbol_table_mat_nat.bs"
        st = self.get_symbols(get_visitor(file))

        input_1 = st.get_local('a', 'main')
        input_2 = st.get_local('b', 'main')
        output = st.get_local('c', 'main')

        assert ChemTypeResolver.is_only_material(input_1.types)
        assert ChemTypeResolver.is_number_in_set(input_2.types) and ChemTypeResolver.is_mat_in_set(input_2.types)
        assert ChemTypeResolver.is_number_in_set(output.types) and ChemTypeResolver.is_mat_in_set(output.types)

    def test_one_undefined(self, get_visitor):
        with pytest.raises(UndefinedVariable):
            file = "test_cases/gradient/symbol_table_one_undefined.bs"
            st = self.get_symbols(get_visitor(file))
