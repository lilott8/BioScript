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

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_single(self, get_visitor):
        file = "test_cases/dispense/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_single_with_index(self, get_visitor):
        file = "test_cases/dispense/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tNOP"
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
                   "\tb[1] = dispense(bbb)\n\tc[0] = mix(a[0], b[0])\n\tc[1] = mix(a[1], b[1])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_one_index_one_no_index(self, get_visitor):
        file = "test_cases/mix/ir_one_index_one_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n" \
                   "\tb[0] = dispense(bbb)\n\tc[0] = mix(a[1], b[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd(self, get_visitor):
        file = "test_cases/mix/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tb[0] = dispense(bbb)\n\tc[0] = mix(a[0], b[0])\n\tNOP"
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
                   "\tc[0] = dispense(aaa)\n\tc[1] = dispense(aaa)\n\tc[0] = mix(a[0], b[0])\n\tNOP"
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
                   "\tx[0] = detect(mod, a[0])\n\tx[1] = detect(mod, a[1])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_lhs_index(self, get_visitor):
        file = "test_cases/detect/ir_sisd_lhs_with_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tx[0] = 1\n\tx[1] = 1\n" \
                   "\tx[0] = detect(mod, a[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_index(self, get_visitor):
        file = "test_cases/detect/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tx[0] = detect(mod, a[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_no_index(self, get_visitor):
        file = "test_cases/detect/ir_sisd_no_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tx[0] = detect(mod, a[0])\n\tNOP"
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
                   "\theat(a[0]) @ 90.0CELSIUS\n\theat(a[1]) @ 90.0CELSIUS\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd(self, get_visitor):
        file = "test_cases/heat/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\theat(a[0]) @ 90.0CELSIUS\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_index(self, get_visitor):
        file = "test_cases/heat/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n" \
                   "\theat(a[0]) @ 90.0CELSIUS\n\tNOP"
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

        expected = "main:\n\ta[0] = dispense(aaa)\n\tb = split(a, 4)\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_simd(self, get_visitor):
        file = "test_cases/split/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tb = split(a, 4)\n\tNOP"
        assert expected == ir.compiled.rstrip()
        assert ir.program.symbol_table.get_local('b', 'main').value.size == 8

    def test_split_an_index(self, get_visitor):
        file = "test_cases/split/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tb = split(a[1], 4)\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/split/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.dispose
class TestDispose(FrontEndBase):

    def test_sisd(self, get_visitor):
        file = "test_cases/dispose/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tdispose(a[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_simd(self, get_visitor):
        file = "test_cases/dispose/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tdispose(a[0])\n\tdispose(a[1])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_index(self, get_visitor):
        file = "test_cases/dispose/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tdispose(a[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/dispose/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.store
class TestStore(FrontEndBase):

    def test_sisd(self, get_visitor):
        file = "test_cases/store/ir_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\tstore(a[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_simd(self, get_visitor):
        file = "test_cases/store/ir_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tstore(a[0])\n\tstore(a[1])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_index(self, get_visitor):
        file = "test_cases/store/ir_sisd_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\tstore(a[0])\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_sisd_out_of_bounds(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/store/ir_sisd_out_of_bounds.bs"
            ir = self.get_compiled_ir(get_visitor(file))


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.math
class TestMath(FrontEndBase):

    def test_sisd_assignment(self, get_visitor):
        file = "test_cases/math/ir_assignment_sisd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 3\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_simd_assignment(self, get_visitor):
        file = "test_cases/math/ir_assignment_simd.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 3\n\ta[1] = 3\n\ta[2] = 3\n\ta[3] = 3\n\tNOP"
        assert expected == ir.compiled.rstrip()
        assert ir.program.symbol_table.get_local('a', 'main').value.size == 4

    def test_add_numbers(self, get_visitor):
        file = "test_cases/math/ir_add_numbers.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 3 + 3\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_add_vars(self, get_visitor):
        file = "test_cases/math/ir_add_vars.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 5\n\tb[0] = 5\n\tc[0] = a[0] + b[0]\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_add_var_number(self, get_visitor):
        file = "test_cases/math/ir_add_var_number.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 5\n\tb[0] = a[0] + 5\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_divide_numbers(self, get_visitor):
        file = "test_cases/math/ir_divide_numbers.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 5 / 4\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_multiply_numbers(self, get_visitor):
        file = "test_cases/math/ir_multiply_numbers.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 5 * 4\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_subtract_numbers(self, get_visitor):
        file = "test_cases/math/ir_subtract_numbers.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 5 - 4\n\tNOP"
        assert expected == ir.compiled.rstrip()

    def test_var_offset_number(self, get_visitor):
        file = "test_cases/math/ir_add_var_offset_number.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "main:\n\ta[0] = 1\n\ta[1] = 1\n\tb[0] = 2 + a[1]\n\tNOP"
        assert expected == ir.compiled.rstrip()


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.if_else
class TestIfElse(FrontEndBase):

    def test_two_numbers(self, get_visitor):
        file = "test_cases/control/ir_if_two_numbers.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tb[0] = 1\n\t\n\tjump: bsbbif_3_f\nbsbbif_3_f:\n\tNOP\nmain:\n\t" \
                   "if 3 > 3\t|\ttrue: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f"
        assert expected == ir.compiled.rstrip()

    def test_var_with_number(self, get_visitor):
        file = "test_cases/control/ir_if_var_number.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tb[0] = 1\n\t\n\tjump: bsbbif_3_f\nbsbbif_3_f:\n\tNOP\nmain:\n\ta[0] = 3\n\t" \
                   "if a[0] > 3\t|\ttrue: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f"
        assert expected == ir.compiled.rstrip()

    def test_var_no_index_size_one(self, get_visitor):
        file = "test_cases/control/ir_if_var_no_index_size_one.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tdispose(a[0])\n\t\n\tjump: bsbbif_3_f\nbsbbif_3_f:\n\tNOP\n" \
                   "main:\n\ta[0] = dispense(aaa)\n\tif a[0] == 8\t|\ttrue: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f"
        assert expected == ir.compiled.rstrip()

    def test_var_with_index(self, get_visitor):
        file = "test_cases/control/ir_if_var_with_index.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tdispose(a[0])\n\t\n\tjump: bsbbif_3_f\nbsbbif_3_f:\n\tNOP\n" \
                   "main:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\t" \
                   "if a[1] == 8\t|\ttrue: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f"
        assert expected == ir.compiled.rstrip()

    def test_var_no_index_not_size_one(self, get_visitor):
        with pytest.raises(InvalidOperation):
            file = "test_cases/control/ir_if_var_no_index_not_size_one.bs"
            ir = self.get_compiled_ir(get_visitor(file))

    def test_nested_if(self, get_visitor):
        file = "test_cases/control/ir_if_nested_ifs.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tif 4 < 2\t|\ttrue: jump bsbbif_4_t\t|\tfalse: jump bsbbif_5_f\nbsbbif_3_f:\n\t" \
                   "dispose(a[0])\n\tNOP\nmain:\n\ta[0] = dispense(aaa)\n\ta[1] = dispense(aaa)\n\t" \
                   "if 2 < 4\t|\ttrue: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f\n" \
                   "bsbbif_4_t:\n\tdispose(a[0])\n\t\n\tjump: bsbbif_5_f\nbsbbif_5_f:\n\t\n\tjump: bsbbif_3_f"
        assert expected == ir.compiled.rstrip()

    def test_if_else(self, get_visitor):
        file = "test_cases/control/ir_if_else.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tx[0] = 3\n\t\n\tjump: bsbbif_4_j\nbsbbif_3_f:\n\tx[0] = 3\n\t\n\t" \
                   "jump: bsbbif_4_j\nbsbbif_4_j:\n\tdispose(a[0])\n\tNOP\nmain:\n\t" \
                   "a[0] = dispense(aaa)\n\tif 3 > 3\t|\ttrue: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f"

        assert expected == ir.compiled.rstrip()

    def test_nested_if_else(self, get_visitor):
        file = "test_cases/control/ir_if_nested_if_else.bs"
        ir = self.get_compiled_ir(get_visitor(file))

        expected = "bsbbif_2_t:\n\tx[0] = 3\n\t\n\tjump: bsbbif_4_j\nbsbbif_3_f:\n\tb[0] = dispense(aaa)\n\t" \
                   "if 3 == 3\t|\ttrue: jump bsbbif_5_t\t|\tfalse: jump bsbbif_6_f\n" \
                   "bsbbif_4_j:\n\tdispose(a[0])\n\tNOP\nmain:\n\ta[0] = dispense(aaa)\n\tif 3 > 3\t|\t" \
                   "true: jump bsbbif_2_t\t|\tfalse: jump bsbbif_3_f\nbsbbif_5_t:\n\tdispose(b[0])\n\t\n\t" \
                   "jump: bsbbif_6_f\nbsbbif_6_f:\n\t\n\tx[0] = 3\n\tjump: bsbbif_4_j"

        assert expected == ir.compiled.rstrip()
