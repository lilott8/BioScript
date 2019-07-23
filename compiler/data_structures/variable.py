from typing import Set

from chemicals.chemtypes import ChemTypes
from compiler.data_structures.properties import *
from shared.bs_exceptions import VariableExpiredError


class Variable(object):

    def __init__(self, name: str, types: set = None, scope: str = "unknown"):
        self.name = name
        self.types = set(types)
        self.scope = scope
        # Used for timing annotations.
        self.use_by = -1
        self.value = None
        # TODO: Delete this.
        self.is_constant = False
        # TODO: Delete this.
        self.is_global = False

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
        super().__init__(var.name, var.types, var.scope)
        self.rename = rename
        self.use_by = var.use_by
        self.points_to = var.name
        self.name = rename
        # TODO: Delete this.
        self.size = var.size


class Fluid(Variable):

    def __init__(self, name: str, types: Set[ChemTypes] = {ChemTypes.MAT}, scope: str = "main", size: int = 1,
                 volume: float = 10.0, units: BSVolume = BSVolume.MICROLITRE):
        super().__init__(name, types, scope)
        self.volume = volume
        self.unit = units
        self.usage = [{'quantity': volume, 'units': units}] * size
        self.value = name
        # TODO: Delete this.
        self.size = len(self.usage) - 1

    def use_fluid(self, volume: float, units: BSVolume, index: int = 0):
        self.usage[index]['quantity'] -= volume
        if self.usage[index]['quantity'] < 0:
            raise VariableExpiredError(
                "Variable {} doesn't have enough volume to complete the operation".format(self.name))

    def __repr__(self):
        output = "Chemical: "
        output += super().__repr__() + "\t"
        output += "{}{}".format(self.volume, self.unit.name)
        return output

    def __str__(self):
        return self.__repr__()


class Movable(Fluid):

    def __init__(self, name: str, types: Set[ChemTypes] = {ChemTypes.MAT}, scope: str = "main",
                 size: int = 1, volume: float = 10.0, units: BSVolume = BSVolume.MICROLITRE):
        super().__init__(name, types, scope, size=size, volume=volume, units=units)


class Stationary(Fluid):

    def __init__(self, name: str, scope: str = "global", types: Set[ChemTypes] = {ChemTypes.MAT}):
        super().__init__(name, types, scope, size=1, volume=float("inf"), units=BSVolume.DECILITRE)
        # TODO: Delete this.
        self.is_global = False


class Module(Variable):

    def __init__(self, name: str, scope: str = "global"):
        super().__init__(name, {ChemTypes.MODULE}, scope)
        # TODO: Delete this.
        self.is_global = False


class Number(Variable):

    def __init__(self, name: str, types: Set[ChemTypes] = {ChemTypes.REAL}, scope: str = "main", value: float = 0):
        super().__init__(name, types, scope)
        self.value = value

    def __repr__(self):
        output = "Number: {}\t".format(super().__repr__())
        output += "value: {}".format(self.value)
        return output

    def __str__(self):
        return self.__repr__()
