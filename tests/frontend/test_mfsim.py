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
     #begin simple unit tests
    def test_mix(self, get_visitor):
        file = "test_cases/mix/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 2, 0, 2, 0, 1, 0])
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

    def test_split(self, get_visitor):
        file = "test_cases/split/ir_sisd.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 1, 0, 3, 0, 0, 3])
        assert expected == counts

    # begin new split size and combination testing
    def test_split_simple_size2(self, get_visitor):
        file = "test_cases/split/simple_size2.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 2, 2, 5, 0, 1, 1])
        assert expected == counts

    def test_split_simple_size4(self, get_visitor):
        file = "test_cases/split/simple_size4.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 2, 4, 9, 0, 1, 3])
        assert expected == counts

    def test_split_simple_size8(self, get_visitor):
        file = "test_cases/split/simple_size8.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 2, 8, 17, 0, 1, 7])
        assert expected == counts

    def test_split_size4_detect(self, get_visitor):
        file = "test_cases/split/size4_detect.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 1, 2, 4, 10, 0, 1, 3])
        assert expected == counts

    def test_split_size4_detect_mix(self, get_visitor):
        file = "test_cases/split/size4_detect_mix.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 1, 3, 4, 12, 0, 2, 3])
        assert expected == counts

    def test_split_size4_heat(self, get_visitor):
        file = "test_cases/split/size4_heat.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 2, 4, 10, 1, 1, 3])
        assert expected == counts

    def test_split_size4_heat_mix(self, get_visitor):
        file = "test_cases/split/size4_heat_mix.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 3, 4, 12, 1, 2, 3])
        assert expected == counts

    #begin exisitng assay tests
    def test_pcr(self, get_visitor):
        file = "test_cases/assays/pcr.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 4, 3, 1, 1, 1, 7, 3, 0, 0])
        assert expected == counts

    def test_prob_pcr(self, get_visitor):
        file = "test_cases/assays/probabilistic_pcr.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([5, 9, 6, 1, 4, 3, 18, 6, 2, 0])
        assert expected == counts

    def test_pcr_droplet_replenishment(self, get_visitor):
        file = "test_cases/assays/pcr_droplet_replenishment.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([4, 8, 5, 1, 4, 1, 17, 5, 3, 0])
        assert expected == counts

    def test_broad_spectrum_opiate(self, get_visitor):
        file = "test_cases/assays/broad_spectrum_opiate.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 5, 10, 5, 20, 0, 5, 0])
        assert expected == counts

    def test_ciprofloxacin(self, get_visitor):
        file = "test_cases/assays/ciprofloxacin.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 0, 3, 1, 9, 4, 17, 2, 5, 0])
        assert expected == counts

    def test_diazepam(self, get_visitor):
        file = "test_cases/assays/diazepam.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([4, 0, 5, 1, 12, 5, 23, 3, 7, 0])
        assert expected == counts

    def test_dilution(self, get_visitor):
        file = "test_cases/assays/dilution.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 6, 6, 21, 0, 5, 5])
        assert expected == counts

    def test_fentanyl(self, get_visitor):
        file = "test_cases/assays/fentanyl.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 2, 3, 1, 6, 3, 16, 2, 5, 0])
        assert expected == counts

    def test_full_morphine(self, get_visitor):
        file = "test_cases/assays/full_morphine.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 0, 3, 3, 24, 9, 48, 6, 15, 0])
        assert expected == counts

    def test_glucose_detection(self, get_visitor):
        file = "test_cases/assays/glucose_detection.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 5, 20, 10, 35, 0, 10, 0])
        assert expected == counts

    def test_heroin(self, get_visitor):
        file = "test_cases/assays/heroin.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 0, 3, 1, 8, 3, 16, 2, 5, 0])
        assert expected == counts

    def test_image_probe_synthesis(self, get_visitor):
        file = "test_cases/assays/image_probe_synthesis.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([0, 0, 1, 0, 4, 1, 13, 6, 3, 0])
        assert expected == counts

    def test_morphine(self, get_visitor):
        file = "test_cases/assays/morphine.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 0, 3, 1, 9, 4, 17, 2, 5, 0])
        assert expected == counts

    def test_ocxycodone(self, get_visitor):
        file = "test_cases/assays/oxycodone.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([2, 0, 3, 1, 8, 3, 16, 2, 5, 0])
        assert expected == counts

    #begin new control assasy tests
    def test_if_else_with_live_droplet_passing(self, get_visitor):
        file = "test_cases/control/if_else_with_live_droplet_passing.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([3, 9, 4, 1, 3, 2, 12, 1, 2, 0])
        assert expected == counts

    def test_nested_repeat(self, get_visitor):
        file = "test_cases/control/nested_repeat.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([4, 6, 4, 1, 1, 1, 9, 4, 0, 0])
        assert expected == counts

    def test_if_else_with_halting(self, get_visitor):
        file = "test_cases/control/if_else_with_halting.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([3, 5, 4, 1, 3, 2, 10, 1, 2, 0])
        assert expected == counts

    def test_repeat_nested_if_else_with_dag6(self, get_visitor):
        file = "test_cases/control/repeat_nested_if_else_with_dag6.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([5, 10, 6, 1, 2, 1, 13, 4, 1, 0])
        assert expected == counts

    def test_repeat_nested_if_else_without_dag6(self, get_visitor):
        file = "test_cases/control/repeat_nested_if_else_without_dag6.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([6, 8, 5, 1, 2, 1, 11, 3, 1, 0])
        assert expected == counts

    def test_repeat_nested_if_with_dag6(self, get_visitor):
        file = "test_cases/control/repeat_nested_if_with_dag6.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([4, 8, 5, 1, 2, 1, 11, 3, 1, 0])
        assert expected == counts

    def test_repeat_nested_if_without_dag6(self, get_visitor):
        file = "test_cases/control/repeat_nested_if_without_dag6.bs"
        counts = self.get_compiled_mfsim(get_visitor(file), file)

        expected = str([5, 6, 4, 1, 2, 1, 9, 2, 1, 0])
        assert expected == counts


# [num_cgs, num_transfers, num_dags, num_detects,
#                 num_dispense, num_dispose, num_edges, num_heats,
#                 num_mixes, num_splits]