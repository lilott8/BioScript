import pytest

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from compiler.data_structures.symbol_table import SymbolTable
from shared.bs_exceptions import UndefinedVariable, UndefinedFunction, UnsupportedOperation
from tests.frontend.front_end_base import FrontEndBase


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.dispose
class TestDispose(FrontEndBase):

    # For whatever reason, this test will fail depending on where you place it. Beware.
    def test_if_else(self, get_visitor):
        file = "test_cases/volume/dispense_if_else.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False

        assert sum(vol[1][-1]['a2']['volumes']) == 10

        for i in range(2):
            assert vol[1][-1]['b1']['volumes'][i] == 2.5

    def test_basic(self, get_visitor):
        file = "test_cases/volume/dispose.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False
        assert sum(vol[1][-1]['a1']['volumes']) == -1


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.dispense
class TestDispense(FrontEndBase):

    def test_basic(self, get_visitor):
        file = "test_cases/volume/dispense_volume.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False
        assert sum(vol[1][-1]['a1']['volumes']) == 50


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.mix
class TestMix(FrontEndBase):

    def test_basic(self, get_visitor):
        file = "test_cases/volume/mix_basic.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False

        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == 20

    def test_offset(self, get_visitor):
        file = "test_cases/volume/mix_single_offset_use.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['a_21']['volumes']) == -1
        assert sum(vol[1][-1]['a_31']['volumes']) == -1
        assert vol[1][-1]['a_s1']['volumes'][0] == 0
        assert vol[1][-1]['a_s1']['volumes'][1] == 10
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == 20

    def test_double_var_use(self, get_visitor):
        file = "test_cases/volume/mix_var_double_use.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0]  # == True

    def test_first_parameter(self, get_visitor):
        file = "test_cases/volume/mix_only_first_parameter.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10

        assert sum(vol[1][1]['a1']['volumes']) == 10
        assert sum(vol[1][1]['b1']['volumes']) == 10

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == 5
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == 15

    def test_second_parameter(self, get_visitor):
        file = "test_cases/volume/mix_only_last_parameter.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10

        assert sum(vol[1][1]['a1']['volumes']) == 10
        assert sum(vol[1][1]['b1']['volumes']) == 10

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == 5
        assert sum(vol[1][-1]['c1']['volumes']) == 15

    def test_both_parameters(self, get_visitor):
        file = "test_cases/volume/mix_both_parameters.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10

        assert sum(vol[1][1]['a1']['volumes']) == 10
        assert sum(vol[1][1]['b1']['volumes']) == 10

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == 5
        assert sum(vol[1][-1]['b1']['volumes']) == 5
        assert sum(vol[1][-1]['c1']['volumes']) == 10


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.split
class TestSplit(FrontEndBase):
    def test_basic(self, get_visitor):
        file = "test_cases/volume/split_basic.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == 10

        for i in range(4):
            assert vol[1][-1]['b1']['volumes'][i] == 2.5

    def test_double_use(self, get_visitor):
        file = "test_cases/volume/split_double_use.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0]  # == True

        assert sum(vol[1][-1]['a1']['volumes']) == -1

    def test_good_num(self, get_visitor):
        file = "test_cases/volume/split_good_num.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert not vol[0]  # == False

        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == 20
        assert vol[1][-1]['b1']['volumes'][0] == 10
        assert vol[1][-1]['b1']['volumes'][1] == 10

    def test_bad_num(self, get_visitor):
        file = "test_cases/volume/split_bad_num.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        assert vol[0]  # == True


@pytest.mark.frontend
@pytest.mark.volume
@pytest.mark.repeat_loop
class TestRepeat(FrontEndBase):
    def test_prob_pcr(self, get_visitor):
        file = "test_cases/assays/probabilistic_pcr.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # TODO: after fixing volume tracking to deal with phi nodes generated from loops, add correct assertions
        assert vol[0]


@pytest.mark.frontend
@pytest.mark.instructions
class TestSimpleMultipleVolumes(FrontEndBase):
    def test_simple_non_phi(self, get_visitor):
        file = "test_cases/volume/simple_non_phi.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['sa1']['volumes']) == 10
        assert sum(vol[1][1]['d11']['volumes']) == 1
        assert sum(vol[1][2]['sas1']['volumes']) == 10
        assert sum(vol[1][3]['d21']['volumes']) == 1
        assert sum(vol[1][4]['first_dilute1']['volumes']) == 11
        assert vol[1][5]['x1']['size'] == 4
        for i in range(4):
            assert vol[1][5]['x1']['volumes'][i] == 2.75
        assert sum(vol[1][6]['second_dilute1']['volumes']) == 11
        assert vol[1][7]['y1']['size'] == 4
        for i in range(4):
            assert vol[1][7]['y1']['volumes'][i] == 2.75

        # Final state tests
        assert sum(vol[1][-1]['sa1']['volumes']) == -1
        assert sum(vol[1][-1]['d11']['volumes']) == -1
        assert sum(vol[1][-1]['sas1']['volumes']) == -1
        assert sum(vol[1][-1]['d21']['volumes']) == -1
        assert sum(vol[1][-1]['first_dilute1']['volumes']) == -1
        assert sum(vol[1][-1]['x1']['volumes']) == -1
        assert sum(vol[1][-1]['second_dilute1']['volumes']) == -1
        assert sum(vol[1][-1]['y1']['volumes']) == -1
        assert sum(vol[1][-1]['z1']['volumes']) == 22

    def test_simple_phi_split(self, get_visitor):
        file = "test_cases/volume/simple_phi_split.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert vol[1][-1]['b1']['size'] == 2
        assert vol[1][-1]['b1']['volumes'][0] == 3
        assert vol[1][-1]['b1']['volumes'][1] == 3
        assert vol[1][-1]['b1']['volumes'][2] == 5
        assert vol[1][-1]['b1']['volumes'][3] == 5

    def test_simple_phi_mix(self, get_visitor):
        file = "test_cases/volume/simple_phi_mix.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert sum(vol[1][4]['b1']['volumes']) == 12
        assert vol[1][5]['c1']['volumes'][0] == 18
        assert vol[1][5]['c1']['volumes'][1] == 22

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1

    def test_simple_detect_phi_mix(self, get_visitor):
        file = "test_cases/volume/simple_detect_phi_mix.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][3]['b1']['volumes']) == 6
        assert sum(vol[1][4]['b2']['volumes']) == 10
        assert vol[1][5]['b3']['volumes'][0] == 6
        assert vol[1][5]['b3']['volumes'][1] == 10
        assert sum(vol[1][5]['b3']['volumes']) == 16
        assert vol[1][6]['c1']['volumes'][0] == 16
        assert vol[1][6]['c1']['volumes'][1] == 20
        assert sum(vol[1][6]['b3']['volumes']) == -1
        assert sum(vol[1][6]['a1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['b3']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1

    def test_simple_phi_mix_split(self, get_visitor):
        file = "test_cases/volume/simple_phi_mix_split.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert sum(vol[1][4]['b1']['volumes']) == 12
        assert vol[1][5]['c1']['volumes'][0] == 18
        assert vol[1][5]['c1']['volumes'][1] == 22

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert vol[1][-1]['d1']['size'] == 2
        assert vol[1][-1]['d1']['volumes'][0] == 9
        assert vol[1][-1]['d1']['volumes'][1] == 9
        assert vol[1][-1]['d1']['volumes'][2] == 11
        assert vol[1][-1]['d1']['volumes'][3] == 11

    def test_simple_phi_split_dispose(self, get_visitor):
        file = "test_cases/volume/simple_phi_split_dispose.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert vol[1][-1]['b1']['size'] == 0
        assert sum(vol[1][-1]['b1']['volumes']) == -1

    def test_simple_phi_split_mix(self, get_visitor):
        file = "test_cases/volume/simple_phi_split_mix.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5
        assert sum(vol[1][5]['c1']['volumes']) == 12
        assert vol[1][6]['d1']['size'] == 2
        assert vol[1][6]['d1']['volumes'][0] == 6
        assert vol[1][6]['d1']['volumes'][1] == 6
        assert vol[1][7]['e1']['volumes'][0] == 18
        assert vol[1][7]['e1']['volumes'][1] == 22

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert vol[1][-1]['b1']['size'] == 0
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1

    def test_simple_phi_mix_specified(self, get_visitor):
        file = "test_cases/volume/simple_phi_mix_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert sum(vol[1][4]['b1']['volumes']) == 12
        assert vol[1][5]['c1']['volumes'][0] == 17
        assert vol[1][5]['a3']['volumes'][0] == 1
        assert vol[1][5]['a3']['volumes'][1] == 5
        assert sum(vol[1][5]['b1']['volumes']) == -1

        # Final state tests
        assert vol[1][-1]['a3']['volumes'][0] == 1
        assert vol[1][-1]['a3']['volumes'][1] == 5
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1

    def test_simple_phi_mix_full_use(self, get_visitor):
        file = "test_cases/volume/simple_phi_mix_full_use.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert sum(vol[1][4]['b1']['volumes']) == 12
        assert vol[1][5]['c1']['volumes'][0] == 17
        assert vol[1][5]['a3']['volumes'][0] == 1
        assert vol[1][5]['a3']['volumes'][1] == 5
        assert sum(vol[1][5]['b1']['volumes']) == -1
        assert sum(vol[1][6]['c1']['volumes']) == -1
        assert sum(vol[1][7]['d1']['volumes']) == 8
        assert vol[1][8]['e1']['volumes'][0] == 9
        assert vol[1][8]['e1']['volumes'][1] == 13
        assert sum(vol[1][8]['d1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1

    def test_simple_phi_split_mix_more_partial_use(self, get_visitor):
        file = "test_cases/volume/simple_phi_split_mix_more_partial_use.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 18
        assert sum(vol[1][2]['a2']['volumes']) == 20
        assert vol[1][3]['a3']['volumes'][0] == 18
        assert vol[1][3]['a3']['volumes'][1] == 20
        assert sum(vol[1][3]['a3']['volumes']) == 38
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 9
        assert vol[1][4]['b1']['volumes'][1] == 9
        assert vol[1][4]['b1']['volumes'][2] == 10
        assert vol[1][4]['b1']['volumes'][3] == 10
        assert sum(vol[1][5]['c1']['volumes']) == 12
        assert sum(vol[1][6]['d1']['volumes']) == 14
        assert vol[1][7]['e1']['volumes'][0] == 17
        assert sum(vol[1][7]['c1']['volumes']) == -1
        assert vol[1][7]['b1']['size'] == 2
        assert vol[1][7]['b1']['volumes'][0] == 4
        assert vol[1][7]['b1']['volumes'][1] == 9
        assert vol[1][7]['b1']['volumes'][2] == 5
        assert vol[1][7]['b1']['volumes'][3] == 10
        assert vol[1][8]['f1']['volumes'][0] == 14
        assert vol[1][8]['f1']['volumes'][1] == 15
        assert sum(vol[1][8]['d1']['volumes']) == 9
        assert vol[1][8]['b1']['size'] == 2
        assert vol[1][8]['b1']['volumes'][0] == 4
        assert vol[1][8]['b1']['volumes'][1] == 0
        assert vol[1][8]['b1']['volumes'][2] == 5
        assert vol[1][8]['b1']['volumes'][3] == 0
        assert vol[1][9]['e1']['volumes'][0] == -1
        assert vol[1][10]['f1']['volumes'][0] == -1
        assert vol[1][11]['g1']['volumes'][0] == 7
        assert sum(vol[1][11]['d1']['volumes']) == 5
        assert vol[1][11]['b1']['volumes'][0] == 1
        assert vol[1][11]['b1']['volumes'][1] == 0
        assert vol[1][11]['b1']['volumes'][2] == 2
        assert vol[1][11]['b1']['volumes'][3] == 0
        assert vol[1][12]['g1']['volumes'][0] == -1
        assert vol[1][13]['h1']['volumes'][0] == 6
        assert vol[1][13]['h1']['volumes'][1] == 7
        assert sum(vol[1][13]['d1']['volumes']) == -1
        assert vol[1][13]['b1']['volumes'][0] == 0
        assert vol[1][13]['b1']['volumes'][1] == 0
        assert vol[1][13]['b1']['volumes'][2] == 0
        assert vol[1][13]['b1']['volumes'][3] == 0

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['f1']['volumes']) == -1
        assert sum(vol[1][-1]['g1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == -1


@pytest.mark.frontend
@pytest.mark.instructions
class TestIndividualMultipleVolumes(FrontEndBase):
    def test_individual_phi_split_mix(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_mix.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5
        assert sum(vol[1][5]['c1']['volumes']) == 12
        assert sum(vol[1][6]['d1']['volumes']) == 14
        assert vol[1][7]['e1']['size'] == 1
        assert vol[1][7]['e1']['volumes'][0] == 15
        assert vol[1][7]['e1']['volumes'][1] == 17
        assert vol[1][7]['b1']['size'] == 2
        assert vol[1][7]['b1']['volumes'][0] == 0
        assert vol[1][7]['b1']['volumes'][1] == 3
        assert vol[1][7]['b1']['volumes'][2] == 0
        assert vol[1][7]['b1']['volumes'][3] == 5
        assert sum(vol[1][7]['c1']['volumes']) == -1
        assert vol[1][8]['f1']['size'] == 1
        assert vol[1][8]['f1']['volumes'][0] == 17
        assert vol[1][8]['f1']['volumes'][1] == 19
        assert vol[1][8]['b1']['volumes'][0] == 0
        assert vol[1][8]['b1']['volumes'][1] == 0
        assert vol[1][8]['b1']['volumes'][2] == 0
        assert vol[1][8]['b1']['volumes'][3] == 0
        assert sum(vol[1][8]['d1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['f1']['volumes']) == -1

    def test_individual_phi_split_mix_swap(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_mix_swap.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5
        assert sum(vol[1][5]['c1']['volumes']) == 12
        assert sum(vol[1][6]['d1']['volumes']) == 14
        assert vol[1][7]['e1']['size'] == 1
        assert vol[1][7]['e1']['volumes'][0] == 15
        assert vol[1][7]['e1']['volumes'][1] == 17
        assert vol[1][7]['b1']['size'] == 2
        assert vol[1][7]['b1']['volumes'][0] == 3
        assert vol[1][7]['b1']['volumes'][1] == 0
        assert vol[1][7]['b1']['volumes'][2] == 5
        assert vol[1][7]['b1']['volumes'][3] == 0
        assert sum(vol[1][7]['c1']['volumes']) == -1
        assert vol[1][8]['f1']['size'] == 1
        assert vol[1][8]['f1']['volumes'][0] == 17
        assert vol[1][8]['f1']['volumes'][1] == 19
        assert vol[1][8]['b1']['volumes'][0] == 0
        assert vol[1][8]['b1']['volumes'][1] == 0
        assert vol[1][8]['b1']['volumes'][2] == 0
        assert vol[1][8]['b1']['volumes'][3] == 0
        assert sum(vol[1][8]['d1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['f1']['volumes']) == -1

    def test_individual_phi_split_mix_direct(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_mix_direct.bs"

        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5
        assert vol[1][5]['e1']['size'] == 1
        assert vol[1][5]['e1']['volumes'][0] == 6
        assert vol[1][5]['e1']['volumes'][1] == 8
        assert vol[1][5]['e1']['volumes'][2] == 10
        assert vol[1][5]['b1']['size'] == 2
        assert vol[1][5]['b1']['volumes'][0] == 0
        assert vol[1][5]['b1']['volumes'][1] == 0
        assert vol[1][5]['b1']['volumes'][2] == 0
        assert vol[1][5]['b1']['volumes'][3] == 0

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1

    def test_individual_phi_split_split(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_split.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5
        assert vol[1][5]['c1']['size'] == 2
        assert vol[1][5]['c1']['volumes'][0] == 1.5
        assert vol[1][5]['c1']['volumes'][1] == 1.5
        assert vol[1][5]['c1']['volumes'][2] == 2.5
        assert vol[1][5]['c1']['volumes'][3] == 2.5
        assert vol[1][5]['b1']['volumes'][0] == 0
        assert vol[1][5]['b1']['volumes'][1] == 3
        assert vol[1][5]['b1']['volumes'][2] == 0
        assert vol[1][5]['b1']['volumes'][3] == 5
        assert vol[1][6]['b1']['volumes'][0] == 0
        assert vol[1][6]['b1']['volumes'][1] == -1
        assert vol[1][6]['b1']['volumes'][2] == 0
        assert vol[1][6]['b1']['volumes'][3] == -1

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1

    def test_individual_phi_split_dispose(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_dispose.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 6
        assert sum(vol[1][2]['a2']['volumes']) == 10
        assert vol[1][3]['a3']['volumes'][0] == 6
        assert vol[1][3]['a3']['volumes'][1] == 10
        assert sum(vol[1][3]['a3']['volumes']) == 16
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 3
        assert vol[1][4]['b1']['volumes'][1] == 3
        assert vol[1][4]['b1']['volumes'][2] == 5
        assert vol[1][4]['b1']['volumes'][3] == 5
        assert vol[1][5]['b1']['volumes'][0] == -1
        assert vol[1][5]['b1']['volumes'][1] == 3
        assert vol[1][5]['b1']['volumes'][2] == -1
        assert vol[1][5]['b1']['volumes'][3] == 5
        assert vol[1][6]['b1']['volumes'][0] == -1
        assert vol[1][6]['b1']['volumes'][1] == -1
        assert vol[1][6]['b1']['volumes'][2] == -1
        assert vol[1][6]['b1']['volumes'][3] == -1

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert vol[1][-1]['b1']['volumes'][0] == -1
        assert vol[1][-1]['b1']['volumes'][1] == -1
        assert vol[1][-1]['b1']['volumes'][2] == -1
        assert vol[1][-1]['b1']['volumes'][3] == -1

    def test_individual_phi_split_mix_specified(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_mix_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 18
        assert sum(vol[1][2]['a2']['volumes']) == 20
        assert vol[1][3]['a3']['volumes'][0] == 18
        assert vol[1][3]['a3']['volumes'][1] == 20
        assert sum(vol[1][3]['a3']['volumes']) == 38
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 9
        assert vol[1][4]['b1']['volumes'][1] == 9
        assert vol[1][4]['b1']['volumes'][2] == 10
        assert vol[1][4]['b1']['volumes'][3] == 10
        assert sum(vol[1][5]['c1']['volumes']) == 12
        assert sum(vol[1][6]['d1']['volumes']) == 14
        assert vol[1][7]['e1']['size'] == 1
        assert vol[1][7]['e1']['volumes'][0] == 17
        assert vol[1][7]['b1']['size'] == 2
        assert vol[1][7]['b1']['volumes'][0] == 4
        assert vol[1][7]['b1']['volumes'][1] == 9
        assert vol[1][7]['b1']['volumes'][2] == 5
        assert vol[1][7]['b1']['volumes'][3] == 10
        assert sum(vol[1][7]['c1']['volumes']) == -1
        assert vol[1][8]['f1']['size'] == 1
        assert vol[1][8]['f1']['volumes'][0] == 14
        assert vol[1][8]['f1']['volumes'][1] == 15
        assert vol[1][8]['b1']['volumes'][0] == 4
        assert vol[1][8]['b1']['volumes'][1] == 0
        assert vol[1][8]['b1']['volumes'][2] == 5
        assert vol[1][8]['b1']['volumes'][3] == 0
        assert sum(vol[1][8]['d1']['volumes']) == 9

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == 9
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['f1']['volumes']) == -1

    def test_individual_phi_split_mix_swap_specified(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_mix_swap_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 18
        assert sum(vol[1][2]['a2']['volumes']) == 20
        assert vol[1][3]['a3']['volumes'][0] == 18
        assert vol[1][3]['a3']['volumes'][1] == 20
        assert sum(vol[1][3]['a3']['volumes']) == 38
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 9
        assert vol[1][4]['b1']['volumes'][1] == 9
        assert vol[1][4]['b1']['volumes'][2] == 10
        assert vol[1][4]['b1']['volumes'][3] == 10
        assert sum(vol[1][5]['c1']['volumes']) == 12
        assert sum(vol[1][6]['d1']['volumes']) == 14
        assert vol[1][7]['e1']['size'] == 1
        assert vol[1][7]['e1']['volumes'][0] == 14
        assert vol[1][7]['e1']['volumes'][1] == 15
        assert vol[1][7]['b1']['size'] == 2
        assert vol[1][7]['b1']['volumes'][0] == 9
        assert vol[1][7]['b1']['volumes'][1] == 0
        assert vol[1][7]['b1']['volumes'][2] == 10
        assert vol[1][7]['b1']['volumes'][3] == 0
        assert sum(vol[1][7]['c1']['volumes']) == 7
        assert vol[1][8]['f1']['size'] == 1
        assert vol[1][8]['f1']['volumes'][0] == 19
        assert vol[1][8]['b1']['volumes'][0] == 4
        assert vol[1][8]['b1']['volumes'][1] == 0
        assert vol[1][8]['b1']['volumes'][2] == 5
        assert vol[1][8]['b1']['volumes'][3] == 0
        assert sum(vol[1][8]['d1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['f1']['volumes']) == -1

    def test_individual_phi_split_mix_direct_specified(self, get_visitor):
        file = "test_cases/volume/individual_phi_split_mix_direct_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][1]['a1']['volumes']) == 18
        assert sum(vol[1][2]['a2']['volumes']) == 20
        assert vol[1][3]['a3']['volumes'][0] == 18
        assert vol[1][3]['a3']['volumes'][1] == 20
        assert sum(vol[1][3]['a3']['volumes']) == 38
        assert vol[1][4]['b1']['size'] == 2
        assert vol[1][4]['b1']['volumes'][0] == 9
        assert vol[1][4]['b1']['volumes'][1] == 9
        assert vol[1][4]['b1']['volumes'][2] == 10
        assert vol[1][4]['b1']['volumes'][3] == 10
        assert vol[1][5]['e1']['size'] == 1
        assert vol[1][5]['e1']['volumes'][0] == 10
        assert vol[1][5]['b1']['size'] == 2
        assert vol[1][5]['b1']['volumes'][0] == 4
        assert vol[1][5]['b1']['volumes'][1] == 4
        assert vol[1][5]['b1']['volumes'][2] == 5
        assert vol[1][5]['b1']['volumes'][3] == 5

        # Final state tests
        assert sum(vol[1][-1]['a3']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1


@pytest.mark.frontend
@pytest.mark.instructions
class TestInlineMultipleVolumes(FrontEndBase):
    def test_inline_simple_foo_bar1(self, get_visitor):
        file = "test_cases/inline/simple_foo_bar1.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][1]['h1']['volumes']) == 10
        assert sum(vol[1][2]['b1']['volumes']) == 20
        assert sum(vol[1][2]['a1']['volumes']) == -1
        assert sum(vol[1][2]['h1']['volumes']) == -1
        assert sum(vol[1][3]['c1']['volumes']) == 10
        assert sum(vol[1][4]['e1']['volumes']) == 10
        assert sum(vol[1][5]['d1']['volumes']) == 20
        assert sum(vol[1][5]['c1']['volumes']) == -1
        assert sum(vol[1][5]['e1']['volumes']) == -1
        assert sum(vol[1][6]['g1']['volumes']) == 40
        assert sum(vol[1][6]['b1']['volumes']) == -1
        assert sum(vol[1][6]['d1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['g1']['volumes']) == -1

    def test_inline_simple_foo_bar1_specified(self, get_visitor):
        file = "test_cases/volume/simple_foo_bar1_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][1]['h1']['volumes']) == 10
        assert sum(vol[1][2]['b1']['volumes']) == 15
        assert sum(vol[1][2]['a1']['volumes']) == -1
        assert sum(vol[1][2]['h1']['volumes']) == 5
        assert sum(vol[1][3]['c1']['volumes']) == 10
        assert sum(vol[1][4]['e1']['volumes']) == 10
        assert sum(vol[1][5]['d1']['volumes']) == 15
        assert sum(vol[1][5]['c1']['volumes']) == 5
        assert sum(vol[1][5]['e1']['volumes']) == -1
        assert sum(vol[1][6]['g1']['volumes']) == 30
        assert sum(vol[1][6]['b1']['volumes']) == -1
        assert sum(vol[1][6]['d1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == 5
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['c1']['volumes']) == 5
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['d1']['volumes']) == -1
        assert sum(vol[1][-1]['g1']['volumes']) == -1

    def test_inline_simple_foo_calls_bar1(self, get_visitor):
        file = "test_cases/inline/simple_foo_calls_bar1.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][1]['g1']['volumes']) == 10
        assert sum(vol[1][2]['e1']['volumes']) == 10
        assert sum(vol[1][3]['h1']['volumes']) == 20
        assert sum(vol[1][3]['e1']['volumes']) == -1
        assert sum(vol[1][3]['g1']['volumes']) == -1
        assert sum(vol[1][4]['b1']['volumes']) == 30
        assert sum(vol[1][4]['h1']['volumes']) == -1
        assert sum(vol[1][4]['a1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['g1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1

    def test_inline_simple_foo_calls_bar1_specified(self, get_visitor):
        file = "test_cases/volume/simple_foo_calls_bar1_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][1]['g1']['volumes']) == 10
        assert sum(vol[1][2]['e1']['volumes']) == 10
        assert sum(vol[1][3]['h1']['volumes']) == 15
        assert sum(vol[1][3]['e1']['volumes']) == 5
        assert sum(vol[1][3]['g1']['volumes']) == -1
        assert sum(vol[1][4]['b1']['volumes']) == 20
        assert sum(vol[1][4]['h1']['volumes']) == -1
        assert sum(vol[1][4]['a1']['volumes']) == 5

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == 5
        assert sum(vol[1][-1]['g1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == 5
        assert sum(vol[1][-1]['h1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1

    def test_inline_simple_multiple_foo_call1(self, get_visitor):
        file = "test_cases/inline/simple_multiple_foo_call1.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][1]['h1']['volumes']) == 10
        assert sum(vol[1][2]['b1']['volumes']) == 20
        assert sum(vol[1][2]['a1']['volumes']) == -1
        assert sum(vol[1][2]['h1']['volumes']) == -1
        assert sum(vol[1][3]['b1']['volumes']) == -1
        assert sum(vol[1][4]['z1']['volumes']) == 10
        assert sum(vol[1][5]['h2']['volumes']) == 10
        assert sum(vol[1][6]['y1']['volumes']) == 20
        assert sum(vol[1][6]['z1']['volumes']) == -1
        assert sum(vol[1][6]['h2']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == -1
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['z1']['volumes']) == -1
        assert sum(vol[1][-1]['h2']['volumes']) == -1
        assert sum(vol[1][-1]['y1']['volumes']) == -1

    def test_inline_simple_multiple_foo_call1_specified(self, get_visitor):
        file = "test_cases/volume/simple_multiple_foo_call1_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['a1']['volumes']) == 10
        assert sum(vol[1][1]['h1']['volumes']) == 10
        assert sum(vol[1][2]['b1']['volumes']) == 10
        assert sum(vol[1][2]['a1']['volumes']) == 5
        assert sum(vol[1][2]['h1']['volumes']) == 5
        assert sum(vol[1][3]['b1']['volumes']) == -1
        assert sum(vol[1][4]['z1']['volumes']) == 10
        assert sum(vol[1][5]['h2']['volumes']) == 10
        assert sum(vol[1][6]['y1']['volumes']) == 10
        assert sum(vol[1][6]['z1']['volumes']) == 5
        assert sum(vol[1][6]['h2']['volumes']) == 5

        # Final state tests
        assert sum(vol[1][-1]['a1']['volumes']) == 5
        assert sum(vol[1][-1]['h1']['volumes']) == 5
        assert sum(vol[1][-1]['b1']['volumes']) == -1
        assert sum(vol[1][-1]['z1']['volumes']) == 5
        assert sum(vol[1][-1]['h2']['volumes']) == 5
        assert sum(vol[1][-1]['y1']['volumes']) == -1

    def test_inline_three_function_chain1_modified(self, get_visitor):
        file = "test_cases/volume/three_function_chain1_modified.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['z1']['volumes']) == 10
        assert sum(vol[1][1]['k1']['volumes']) == 10
        assert sum(vol[1][2]['g1']['volumes']) == 10
        assert sum(vol[1][3]['e1']['volumes']) == 10
        assert sum(vol[1][4]['h1']['volumes']) == 20
        assert sum(vol[1][4]['g1']['volumes']) == -1
        assert sum(vol[1][4]['e1']['volumes']) == -1
        assert sum(vol[1][5]['l1']['volumes']) == 30
        assert sum(vol[1][5]['h1']['volumes']) == -1
        assert sum(vol[1][5]['k1']['volumes']) == -1
        assert sum(vol[1][6]['y1']['volumes']) == 40
        assert sum(vol[1][6]['z1']['volumes']) == -1
        assert sum(vol[1][6]['l1']['volumes']) == -1

        # Final state tests
        assert sum(vol[1][-1]['z1']['volumes']) == -1
        assert sum(vol[1][-1]['k1']['volumes']) == -1
        assert sum(vol[1][-1]['g1']['volumes']) == -1
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == -1
        assert sum(vol[1][-1]['l1']['volumes']) == -1
        assert sum(vol[1][-1]['y1']['volumes']) == -1

    def test_inline_three_function_chain1_modified_specified(self, get_visitor):
        file = "test_cases/volume/three_function_chain1_modified_specified.bs"
        tree = get_visitor(file)

        vol = self.get_volume_inline(tree, file)

        # Failure test
        assert not vol[0]  # == False

        # Middle state tests
        assert sum(vol[1][0]['z1']['volumes']) == 10
        assert sum(vol[1][1]['k1']['volumes']) == 10
        assert sum(vol[1][2]['g1']['volumes']) == 10
        assert sum(vol[1][3]['e1']['volumes']) == 10
        assert sum(vol[1][4]['h1']['volumes']) == 15
        assert sum(vol[1][4]['g1']['volumes']) == 5
        assert sum(vol[1][4]['e1']['volumes']) == -1
        assert sum(vol[1][5]['l1']['volumes']) == 15
        assert sum(vol[1][5]['h1']['volumes']) == 10
        assert sum(vol[1][5]['k1']['volumes']) == -1
        assert sum(vol[1][6]['y1']['volumes']) == 15
        assert sum(vol[1][6]['z1']['volumes']) == -1
        assert sum(vol[1][6]['l1']['volumes']) == 10

        # Final state tests
        assert sum(vol[1][-1]['z1']['volumes']) == -1
        assert sum(vol[1][-1]['k1']['volumes']) == -1
        assert sum(vol[1][-1]['g1']['volumes']) == 5
        assert sum(vol[1][-1]['e1']['volumes']) == -1
        assert sum(vol[1][-1]['h1']['volumes']) == 10
        assert sum(vol[1][-1]['l1']['volumes']) == 10
        assert sum(vol[1][-1]['y1']['volumes']) == -1
