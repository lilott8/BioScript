import pytest

from shared.bs_exceptions import InvalidOperation
from tests.frontend.front_end_base_inline_flag import FrontEndBase


@pytest.mark.frontend
@pytest.mark.target
@pytest.mark.instructions
@pytest.mark.MFSim
class TestMFSim(FrontEndBase):
    """
        These tests are very rudimentary, as they simply count the number
        of various elements of an MFSim CFG/DAGs:
        expected for each will be a list of the elements:
        [num_cgs, num_transfers, num_dags, num_detects,
                num_dispense, num_dispose, num_edges, num_heats,
                num_mixes, num_splits, num_exps]
        Added num_exps to better tell if the cfg file remains the same after changes
    """
     #begin simple foo bar call tests
    def test_simple_foo_bar1(self, get_visitor):
        file = "test_cases/inline/simple_foo_bar1.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 4, 1, 7, 0, 3, 0, 0])
        assert expected == counts

    def test_simple_foo_bar2(self, get_visitor):
        file = "test_cases/inline/simple_foo_bar2.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 4, 1, 7, 0, 3, 0, 0])
        assert expected == counts

    def test_simple_foo_bar3(self, get_visitor):
        file = "test_cases/inline/simple_foo_bar3.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 5, 1, 9, 0, 4, 0, 0])
        assert expected == counts

    #begin mutliple foo call tests
    def test_simple_multiple_foo_call1(self, get_visitor):
        file = "test_cases/inline/simple_multiple_foo_call1.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 4, 2, 6, 0, 2, 0, 0])
        assert expected == counts

    def test_simple_multiple_foo_call2(self, get_visitor):
        file = "test_cases/inline/simple_multiple_foo_call2.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 6, 3, 9, 0, 3, 0, 0])
        assert expected == counts

    def test_simple_multiple_foo_call3(self, get_visitor):
        file = "test_cases/inline/simple_multiple_foo_call3.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 9, 2, 16, 0, 7, 0, 0])
        assert expected == counts

    #begin simple foo calls bar tests
    def test_simple_foo_calls_bar1(self, get_visitor):
        file = "test_cases/inline/simple_foo_calls_bar1.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 3, 1, 5, 0, 2, 0, 0])
        assert expected == counts

    def test_simple_foo_calls_bar2(self, get_visitor):
        file = "test_cases/inline/simple_foo_calls_bar2.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 6, 1, 11, 0, 5, 0, 0])
        assert expected == counts

    def test_simple_foo_calls_bar3(self, get_visitor):
        file = "test_cases/inline/simple_foo_calls_bar3.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 5, 1, 9, 0, 4, 0, 0])
        assert expected == counts

    #begin three function chain tests
    def test_three_function_chain1(self, get_visitor):
        file = "test_cases/inline/three_function_chain1.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 10, 3, 17, 0, 7, 0, 0])
        assert expected == counts

    def test_three_function_chain2(self, get_visitor):
        file = "test_cases/inline/three_function_chain2.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 14, 4, 24, 0, 10, 0, 0])
        assert expected == counts

    def test_three_function_chain3(self, get_visitor):
        file = "test_cases/inline/three_function_chain3.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 12, 4, 20, 0, 8, 0, 0])
        assert expected == counts

    def test_three_function_chain4(self, get_visitor):
        file = "test_cases/inline/three_function_chain4.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 10, 4, 16, 0, 6, 0, 0])
        assert expected == counts

    #begin long three function chain tests
    def test_long_three_function_chain1(self, get_visitor):
        file = "test_cases/inline/long_three_function_chain1.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 18, 6, 30, 0, 12, 0, 0])
        assert expected == counts

    def test_long_three_function_chain2(self, get_visitor):
        file = "test_cases/inline/long_three_function_chain2.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 18, 5, 31, 0, 13, 0, 0])
        assert expected == counts

# [num_cgs, num_transfers, num_dags, num_detects,
#                 num_dispense, num_dispose, num_edges, num_heats,
#                 num_mixes, num_splits, num_exps]