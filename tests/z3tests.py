import unittest
import functools
from solvers.z3_solver import Z3Solver

class Z3Tests(unittest.TestCase):


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
            if t1 in self.reactive_table[t2]:
                return False
        return True


    def test_z3solver(self):
        table = Z3Tests.build_interaction_table('resources/abstract-interaction.txt')
        a = Z3Solver.solve_constraints('resources/tetracholorethylene_and_nitric_acid.json', functools.partial(Z3Tests.validate, table))
        b = Z3Solver.solve_constraints('resources/hexane_explosion.json', functools.partial(Z3Tests.validate, table))
        print(a)
        print(b)










