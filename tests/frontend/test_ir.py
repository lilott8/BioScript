import pytest

from shared.bs_exceptions import InvalidOperation
from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.dispense
class TestDispense(FrontEndBase):

    def test_array(self, get_visitor):
        file = "test_cases/dispense/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)"
        assert expected == ir.compiled.rstrip()

    def test_single(self, get_visitor):
        file = "test_cases/dispense/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)"
        assert expected == ir.compiled.rstrip()

    def test_single_with_index(self, get_visitor):
        file = "test_cases/dispense/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)"
        assert expected == ir.compiled.rstrip()


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.mix
class TestMix(FrontEndBase):

    def test_simd_no_index(self, get_visitor):
        file = "test_cases/mix/ir_simd_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tb[0] = dispense(bbb)\n" \
                   "\tb[1] = dispense(bbb)\n\tc[0] = mix(a[0], b[0])\n\tc[1] = mix(a[1], b[1])"
        assert expected == ir.compiled.rstrip()

    def test_one_index_one_no_index(self, get_visitor):
        file = "test_cases/mix/ir_one_index_one_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n" \
                   "\tb[0] = dispense(bbb)\n\tc[0] = mix(a[1], b[0])"
        assert expected == ir.compiled.rstrip()

    def test_sisd(self, get_visitor):
        file = "test_cases/mix/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tb[0] = dispense(bbb)\n\tc[0] = mix(a[0], b[0])"
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

        expected = "main:\n\ta[0] = dispense(aaa)\n\tb[0] = dispense(bbb)\n" \
                   "\tc[0] = dispense(aaa)\n\tc[1] = dispense(aaa)\n\tc[0] = mix(a[0], b[0])"
        assert expected == ir.compiled.rstrip()


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.detect
class TestDetect(FrontEndBase):

    def test_simd(self, get_visitor):
        file = "test_cases/detect/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n" \
                   "\tx[0] = detect(mod, a[0])\n\tx[1] = detect(mod, a[1])"
        assert expected == ir.compiled.rstrip()

    def test_sisd_lhs_index(self, get_visitor):
        file = "test_cases/detect/ir_sisd_lhs_with_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tb[0] = dispense(bbb)\n" \
                   "\tb[1] = dispense(bbb)\n\tc[0] = mix(a[0], b[0])\n\tc[1] = mix(a[1], b[1])"
        assert expected == ir.compiled.rstrip()

    def test_sisd_index(self, get_visitor):
        file = "test_cases/detect/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tx[0] = detect(mod, a[0])"
        assert expected == ir.compiled.rstrip()

    def test_sisd_no_index(self, get_visitor):
        file = "test_cases/detect/ir_sisd_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tx[0] = detect(mod, a[0])"
        assert expected == ir.compiled.rstrip()

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/detect/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.heat
class TestHeat(FrontEndBase):

    def test_simd(self, get_visitor):
        file = "test_cases/heat/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n" \
                   "\theat(a[0]) @ 90.0CELSIUS\n\theat(a[1]) @ 90.0CELSIUS"
        assert expected == ir.compiled.rstrip()

    def test_sisd(self, get_visitor):
        file = "test_cases/heat/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\theat(a[0]) @ 90.0CELSIUS"
        assert expected == ir.compiled.rstrip()

    def test_sisd_index(self, get_visitor):
        file = "test_cases/heat/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n" \
                   "\theat(a[0]) @ 90.0CELSIUS"
        assert expected == ir.compiled.rstrip()

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/heat/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.split
class TestSplit(FrontEndBase):

    def test_sisd(self, get_visitor):
        file = "test_cases/split/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tb = split(a, 4)"
        assert expected == ir.compiled.rstrip()

    def test_simd(self, get_visitor):
        file = "test_cases/split/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tb = split(a, 4)"
        assert expected == ir.compiled.rstrip()
        assert ir.program.symbol_table.get_local('b', 'main').value.size == 8

    def test_split_an_index(self, get_visitor):
        file = "test_cases/split/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tb = split(a[1], 4)"
        assert expected == ir.compiled.rstrip()

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/split/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))
