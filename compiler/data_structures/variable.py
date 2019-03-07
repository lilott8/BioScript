from chemicals.chemtypes import ChemTypes
from compiler.data_structures.properties import *


class Variable(object):

    def __init__(self, name: str, types: set = None, scope: str = "unknown", size: int = 1,
                 is_global: bool = False):
        self.name = name
        self.types = types
        self.scope = scope
        self.size = size
        self.is_declared = False
        self.is_global = is_global
        # Used for timing annotations.
        self.use_by = -1
        if self.types is None:
            self.types = set()
            self.types.add(ChemTypes.UNKNOWN)

    def __repr__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}".format(self.name)
        output += "\tsize: {}".format(self.size)
        output += "\t({})".format(self.scope)
        return output


class RenamedVar(Variable):

    def __init__(self, rename: str, var: Variable):
        super().__init__(var.name, var.types, var.scope, var.size, var.is_global)
        self.rename = rename
        self.use_by = var.use_by
        self.points_to = var.name
        self.name = rename


class Chemical(Variable):

    def __init__(self, name: str, types: set = {ChemTypes.UNKNOWN}, scope: str = "unknown", size: int = 1,
                 is_global: bool = False, stationary: bool = False, volume: float = 10.0,
                 units: BSVolume = BSVolume.MICROLITRE):
        super().__init__(name, types, scope, size, is_global)
        self.stationary = stationary
        self.volume = volume
        self.unit = units

    def __repr__(self):
        output = super().__repr__() + "\n"
        output += "Chemical: {}{}".format(self.volume, self.unit.name)
        return output


class Number(Variable):

    def __init__(self, name: str, types: frozenset = None, scope: str = "unknown", size: int = 1,
                 is_global: bool = False, value: float = 0):
        super().__init__(name, types, scope, size, is_global)
        self.value = value

    def __repr__(self):
        output = super().__repr__()
        output += "Number: {}".format(self.value)
        return output
