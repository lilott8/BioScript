import copy
from typing import Set, List, Dict

from chemicals.chemtypes import ChemTypes
from compiler.data_structures.variable import Variable


class Function(object):

    def __init__(self, name: str, return_types: Set[ChemTypes] = set(), arguments: List[str] = list(),
                 return_var: Variable = None):
        self.name = name
        self.types = return_types
        # This is a dictionary of: {'name': str, 'types': Set[ChemTypes]}
        # This will help weave the actual arguments that are discovered
        # elsewhere into the correct state.
        self._temp_args = arguments
        # This is the actual argument list for the method.
        self._args = list()
        # This is a string.
        self.return_var = return_var

    @property
    def args(self):
        return self._args

    @args.setter
    def args(self, element: Variable):
        arg = copy.deepcopy(element['var'])
        arg.scope = self.name
        arg.name = self._temp_args[len(self._args) - 1]
        self._args.append(arg)

    @property
    def size(self):
        if not self.return_var:
            return -1
        else:
            return self.return_var.size

    @size.setter
    def size(self, arg: Dict):
        pass

    def __str__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}\t{{".format(self.name)
        if self.args:
            for arg in self.args:
                output += "{}, ".format(arg.name)
            output = output[:-2]
        output += "}"
        return output

    def __repr__(self):
        return self.__str__()
