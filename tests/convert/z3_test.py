import functools

from storage.solvers.z3_solver import Z3Solver


def test_z3solver():
    table = Z3Tests.build_interaction_table('resources/abstract-interaction.txt')
    safe = functools.partial(Z3Tests.validate, table)

    a = Z3Solver.solve_constraints('resources/chemstor/tetracholorethylene_and_nitric_acid.json', safe, sol=True)
    b = Z3Solver.solve_constraints('resources/chemstor/hexane_explosion.json', safe, sol=True)
    c = Z3Solver.solve_constraints('resources/chemstor/methanol_and_nitric_acid.json', safe, sol=True)
    d = Z3Solver.solve_constraints('resources/chemstor/full_cabinet.json', safe, sol=True)
    e = Z3Solver.solve_constraints('resources/chemstor/benzene_urea_benzotricholoride.json', safe_funct=lambda x,y:True, sol=True)
    f = Z3Solver.solve_constraints('resources/chemstor/combine_two_tests.json', safe_funct=lambda x,y:True, sol=True)
    g = Z3Solver.solve_constraints('resources/chemstor/lithium_aluminum_hydride_fire.json', sol=True)
    h = Z3Solver.solve_constraints('resources/chemstor/lithium_aluminum_hydride_fire.json', safe_funct=lambda x,y:True, sol=True)
    i = Z3Solver.solve_constraints('resources/chemstor/hydrogen_peroxide_sulfuric_acid_acetone.json', safe_funct=lambda x,y:True, sol=True)
    j = Z3Solver.solve_constraints('resources/chemstor/hydrogen_peroxide_sulfuric_acid_acetone.json', safe_funct=lambda x,y:False, sol=True)
    k = Z3Solver.solve_constraints('resources/chemstor/benzene_formaldehyde.json', safe_funct=lambda x,y:True, sol=True)
    l = Z3Solver.solve_constraints('resources/chemstor/benzene_formaldehyde.json', safe_funct=lambda x,y:False, sol=True)
    m = Z3Solver.solve_constraints('resources/chemstor/sodium_hydroxide_allyl_ethyl_ether_cycloheptatriene_chlorotrifluormethane_isopropyl_alcohol.json', safe_funct=lambda x,y:True, sol=True)
    n = Z3Solver.solve_constraints('resources/chemstor/sodium_hydroxide_allyl_ethyl_ether_cycloheptatriene_chlorotrifluormethane_isopropyl_alcohol.json', safe_funct=lambda x,y:False, sol=True)
    assert not a
    assert not b
    assert not c
    assert not d
    assert e
    assert f
    assert not g
    assert h
    assert i
    assert not j
    assert k
    assert not l
    assert m
    assert not n
    return e, f, h, i, k, m


#@pytest.mark.skip
class Z3Tests(object):

    #@pytest.mark.skip
    @staticmethod
    def build_interaction_table(file_name: str) -> dict:
        """
        Build the abstract interaction table.
        :param file_name: path to abstract interaction table.
        :return: dict of the abstract interaction table.
        """
        result = dict()
        with open(file_name, 'r') as file_read:
            z = 0
            for line in file_read:
                line = line.strip()
                if z == 0:
                    z += 1
                    continue
                keys = line.strip().split("|")
                row = int(keys[0])
                column = int(keys[1])
                output = set()
                for a in keys[2].split("_"):
                    output.add(int(a))
                if row not in result:
                    result[row] = dict()
                result[row][column] = output
        return result

    #@pytest.mark.skip
    def validate(table, t1, t2) -> bool:
        """
        Checks for a valid interaction.
        :param t1: ChemTypes demonstrating a reactive group.
        :param t2: ChemTypes demonstrating a reactive group.
        :return: True is the groups can interact.
        """
        # Check the regular way.
        if t1 in table:
            if t2 in table[t1]:
                return False
        # Check the inverse.
        if t2 in table:
            if t1 in table[t2]:
                return False
        return True


