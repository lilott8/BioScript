import pytest

from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.ir
@pytest.mark.instructions
@pytest.mark.dispense
class TestDispense(FrontEndBase):

    def test_array(self, get_visitor):
        file = "test_cases/dispense/ir_array.bs"
        st = self.get_program(get_visitor(file))

    def test_single(self, get_visitor):
        file = "test_cases/dispense/ir_single.bs"
        st = self.get_program(get_visitor(file))

    def test_single_with_index(self, get_visitor):
        file = "test_cases/dispense/ir_single_index.bs"
        st = self.get_program(get_visitor(file))
