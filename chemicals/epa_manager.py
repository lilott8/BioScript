import json

import colorlog

from chemicals.chemtypes import ChemTypes
from chemicals.chemtypes import Consequence
from chemicals.reactive_group import ReactiveGroup


class EpaManager(object):

    def __init__(self, epa_defs_file_name: str, interaction_file_name: str):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.interactions = EpaManager.build_interaction_table(interaction_file_name)
        # We store both the entire reactive groups and the associated data in conjunction with
        # The simplified table.  This is only to make access less verbose.
        (self.reactive_groups, self.reactive_table) = EpaManager.build_reactive_table(epa_defs_file_name)

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

    @staticmethod
    def build_reactive_table(file_name: str) -> tuple:
        """
        Build the EPA reactivity table.
        :param file_name: path to the epa_defs.json file.
        :return: tuple of the constructed EPA reactivity table and
            corresponding groups.
        """
        reactive_groups = {}
        reactive_table = {}

        with open(file_name) as file_read:
            for group in json.loads(file_read.read())['chemicalgroups']['group']:
                rid = ChemTypes(int(group['id']))
                name = group['name']

                filters = {'smiles': set(), 'smarts': set(), 'elements': set(), 'words': ()}
                for smile in group['classifiers']['smiles']:
                    filters['smiles'].add(smile)

                for smart in group['classifiers']['smarts']:
                    filters['smarts'].add(smart)

                reactivegroups = dict()
                if 'reactivegroups' in group and group['reactivegroups'] is not None:
                    for rg in group['reactivegroups']['reaction']:
                        reactivegroups[int(rg['id'])] = Consequence.from_string(rg['outcome'])
                reactive_table[rid] = reactivegroups
                reactive_groups[rid] = ReactiveGroup(rid, name, filters, reactivegroups)
        return reactive_groups, reactive_table

    def check_reactive_table(self, x, y):
        return x in self.reactive_table and y in self.reactive_table[x]

    def check_interactions(self, x, y):
        return x in self.interactions and y in self.interactions[x]

    def get_sparse_matrix_at_index(self, x, y):
        return self.reactive_table[x][y]

    def get_consequence(self, t1: ChemTypes, t2: ChemTypes) -> Consequence:
        return self.reactive_table[t1][t1]

    def validate(self, t1: ChemTypes, t2: ChemTypes) -> bool:
        """
        Checks for a valid interaction.
        :param t1: ChemTypes demonstrating a reactive group.
        :param t2: ChemTypes demonstrating a reactive group.
        :return: True is the groups can interact.
        """
        # Check the regular way.
        if t1 in self.reactive_table:
            if t2 in self.reactive_table[t1]:
                return False
        # Check the inverse.
        if t2 in self.reactive_table:
            if t1 in self.reactive_table[t2]:
                return False
        return True

    def get_interaction_result(self, t1: ChemTypes, t2: ChemTypes) -> set:
        """
        Get the resulting types from an interaction.
        :param t1: ChemTypes demonstrating a reactive group.
        :param t2: ChemTypes demonstrating a reactive group.
        :return: Set of resulting types.
        """
        if t1 in self.interactions:
            if t2 in self.interactions[t1]:
                return self.interactions[t1][t2]
        if t2 in self.interactions:
            if t1 in self.interactions[t2]:
                return self.interactions[t2][t1]
        return set()
