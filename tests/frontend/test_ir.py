import pytest

from shared.bs_exceptions import InvalidOperation
from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.dispense
class TestDispense(FrontEndBase):

    def test_array(self, get_visitor):
        file = "test_cases/dispense/ir_array.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)\na[1] = dispense(aaa)"
        assert expected == ir.compiled.rstrip()

    def test_single(self, get_visitor):
        file = "test_cases/dispense/ir_single.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)"
        assert expected == ir.compiled.rstrip()

    def test_single_with_index(self, get_visitor):
        file = "test_cases/dispense/ir_single_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)"
        assert expected == ir.compiled.rstrip()


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.mix
class TestMix(FrontEndBase):

    def test_simd_no_index(self, get_visitor):
        file = "test_cases/mix/ir_simd_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)\na[1] = dispense(aaa)\nb[0] = dispense(bbb)\n" \
                   "b[1] = dispense(bbb)\nc[0] = mix(a[0], b[0])\nc[1] = mix(a[1], b[1])"
        assert expected == ir.compiled.rstrip()

    def test_one_index_one_no_index(self, get_visitor):
        file = "test_cases/mix/ir_one_index_one_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)\na[1] = dispense(aaa)\nb[0] = dispense(bbb)\nc[0] = mix(a[1], b[0])"
        assert expected == ir.compiled.rstrip()

    def test_sisd(self, get_visitor):
        file = "test_cases/mix/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)\nb[0] = dispense(bbb)\nc[0] = mix(a[0], b[0])"
        assert expected == ir.compiled.rstrip()

    def test_simd_unequal(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/mix/ir_simd_unequal_arrays.bs"
            ir = self.get_compiled_ir(get_visitor(file))

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/mix/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))

    def test_sisd_out_of_bounds_second_var(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/mix/ir_sisd_out_of_bounds_second_var.bs"
            ir = self.get_compiled_ir(get_visitor(file))

    def test_sisd_variable_exists(self, get_visitor):
        file = "test_cases/mix/ir_sisd_variable_exists.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "a[0] = dispense(aaa)\nb[0] = dispense(bbb)\nc[0] = dispense(aaa)\n" \
                   "c[1] = dispense(aaa)\nc[0] = mix(a[0], b[0])"
        assert expected == ir.compiled.rstrip()
