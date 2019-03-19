from chemicals.chemtypes import ChemTypes
from compiler.data_structures.properties import *


class Variable(object):

    def __init__(self, name: str, types: set = None, scope: str = "unknown", size: int = 1,
                 is_global: bool = False, is_constant: bool = False):
        self.name = name
        self.types = types
        self.scope = scope
        self.size = size
        self.is_declared = False
        self.is_global = is_global
        self.is_constant = is_constant
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

    def __str__(self):
        return self.__repr__()


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
        output = "Chemical: "
        output += super().__repr__() + "\t"
        output += "{}{}".format(self.volume, self.unit.name)
        return output

    def __str__(self):
        return self.__repr__()


class Number(Variable):

    def __init__(self, name: str, types: set = None, scope: str = "unknown", size: int = 1,
                 is_global: bool = False, value: float = 0, is_constant: bool = False):
        super().__init__(name, types, scope, size, is_global, is_constant)
        self.value = value

    def __repr__(self):
        output = "Number: {}\t".format(super().__repr__())
        output += "value: {}".format(self.value)
        return output

    def __str__(self):
        return self.__repr__()
