import pytest

from shared.bs_exceptions import InvalidOperation
from tests.frontend.front_end_base import FrontEndBase


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
                num_mixes, num_splits]
    """

    def test_mix(self, get_visitor):
        file = "test_cases/mix/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 2, 0, 2, 0, 1, 0])
        assert expected == counts

    def test_split(self, get_visitor):
        file = "test_cases/split/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 1, 0, 1, 0, 0, 1])
        assert expected == counts

    def test_heat(self, get_visitor):
        file = "test_cases/heat/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 1, 0, 1, 1, 0, 0])
        assert expected == counts

    def test_dispose(self, get_visitor):
        file = "test_cases/dispose/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 1, 1, 1, 0, 0, 0])
        assert expected == counts

    def test_dispense(self, get_visitor):
        file = "test_cases/dispense/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 1, 0, 0, 0, 0, 0])
        assert expected == counts

    def test_detect(self, get_visitor):
        file = "test_cases/detect/ir_sisd_no_index.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 1, 1, 0, 1, 0, 0, 0])
        assert expected == counts

    # def test_pcr(self, get_visitor):
    #     file = "test_cases/assays/pcr.bs"
    #     counts = self.get_compiled_mfsim(get_visitor(file), file)
    #
    #     expected = str([2, 4, 3, 1, 1, 1, 7, 3, 0, 0])
    #     assert expected == counts

    def test_prob_pcr(self, get_visitor):
        file = "test_cases/assays/probabilistic_pcr.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([5, 9, 6, 1, 2, 1, 14, 6, 1, 0])
        assert expected == counts

# [num_cgs, num_transfers, num_dags, num_detects,
#                 num_dispense, num_dispose, num_edges, num_heats,
#                 num_mixes, num_splits]