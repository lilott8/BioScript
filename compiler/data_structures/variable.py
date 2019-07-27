from abc import ABCMeta, abstractmethod
from typing import Set, Any

import colorlog

from chemicals.chemtypes import ChemTypes
from compiler.data_structures.properties import *


class Variable(metaclass=ABCMeta):

    def __init__(self, name: str, types: set = None, scope: str = "unknown"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = name
        self._types = set(types)
        self.scope = scope
        # Used for timing annotations.
        self._annotations = dict()
        self._value = None
        # TODO: Delete this.
        self.is_constant = False
        # TODO: Delete this.
        self.is_global = False
        # The observer related members.
        self.observers = set()
        self._subject_state = None

    @property
    @abstractmethod
    def size(self):
        pass

    @property
    @abstractmethod
    def value(self):
        pass

    @value.setter
    @abstractmethod
    def value(self, val: Any):
        pass

    @property
    def types(self):
        return self._types

    @types.setter
    def types(self, typez: set):
        self._types.update(typez)

    @property
    def annotations(self):
        return self._annotations

    @annotations.setter
    def annotations(self, annot: Dict):
        self._annotations[annot['key']] = annot['value']

    def __repr__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}".format(self.name)
        output += "\t({})".format(self.scope)
        return output

    def __str__(self):
        return self.__repr__()


class RenamedVar(Variable):

    def __init__(self, rename: str, var: Variable):
        super().__init__(var.name, var.types, var.scope)
        self.rename = rename
        self._annotations = var._annotations
        self.points_to = var.name
        self.name = rename
        self._value = var.value

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, val: str):
        self._value = val

    @property
    def size(self):
        if isinstance(self._value, (int, float, complex)):
            return 1
        else:
            return len(self._value)


class Reagent(Variable, metaclass=ABCMeta):

    def __init__(self, name: str, types: Set[ChemTypes], scope: str, size: int, volume: float, units: BSVolume):
        super().__init__(name, types, scope)
        self._value = dict()
        for x in range(0, size):
            self._value[x] = FluidProperties(volume=units.normalize(volume), vol_units=BSVolume.MICROLITRE)

    @property
    def size(self):
        return len(self._value)

    @property
    def volume(self) -> Dict:
        """
        Compute the volume of a fluid
        by iterating through the value.
        :return: Dict of volume information.
        """
        total = 0
        for k, v in self._value.items():
            if v.volume['units'] != BSVolume.MICROLITRE:
                total += v.volume['units'].normalize(v.volume['quantity'])
            else:
                total += v.volume['quantity']
        return {"quantity": total, "units": BSVolume.MICROLITRE}

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, val: Dict):
        """
        Changes the value of this variable.
        This is where volume, concentration,
        viscosity, density, etc will be
        manipulated. As the volume changes,
        some of the dependent attributes will
        change in suite as well.  This property
        is the place to manage this.

        The form of the dict can be in 4 forms:
        "op" can be: {mix | split | use | heat}
        The [index] can only be an int and it *must* reference
        a valid index within the variable's value array.

        mix:
            see @compiler.data_structures.properties.FluidProperties.volume
        use:
            see @compiler.data_structures.properties.FluidProperties.volume
        split:
            {'op': 'split', 'values': {'size': [int]}}
        heat:
            see @compiler.data_structures.properties.FluidProperties.temperature

        :param val: Dict of indexes to use volume.
        :return: None.
        """
        if val['op'] == 'mix' or val['op'] == 'use':
            for k, v in val['values'].items():
                self._value[k].volume = {'op': val['op'], 'values': v}
        elif val['op'] == 'split':
            pass
        elif val['op'] == 'heat':
            for k, v in val['values'].items():
                self._value[k].temperature = {'op': val['op'], 'values': v}

    def __repr__(self):
        output = "Chemical: "
        output += super().__repr__() + "\t"
        output += "size: {}\t{}".format(self.size, self.volume)
        return output

    def __str__(self):
        return self.__repr__()


class Movable(Reagent):

    def __init__(self, name: str, types: Set[ChemTypes] = {ChemTypes.MAT}, scope: str = "main",
                 size: int = 1, volume: float = 0, units: BSVolume = BSVolume.MICROLITRE):
        super().__init__(name, types, scope, size=size, volume=volume, units=units)


class Stationary(Reagent):

    def __init__(self, name: str, scope: str = "global", types: Set[ChemTypes] = {ChemTypes.MAT}):
        super().__init__(name, types, scope, size=1, volume=float("inf"), units=BSVolume.DECILITRE)
        # TODO: Delete this.
        self.is_global = True


class Module(Variable):

    def __init__(self, name: str, scope: str = "global"):
        super().__init__(name, {ChemTypes.MODULE}, scope)
        # TODO: Delete this.
        self._value = name
        self.is_global = False

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, val: str):
        self._value = val

    @property
    def size(self):
        return 1


class Number(Variable):

    def __init__(self, name: str, types: Set[ChemTypes] = {ChemTypes.REAL}, scope: str = "main", value: float = 0):
        super().__init__(name, types, scope)

    def __repr__(self):
        output = "Number: {}\t".format(super().__repr__())
        output += "value: {}".format(self.value)
        return output

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, val: float):
        self._value = val

    @property
    def size(self):
        return 1

    def __str__(self):
        return self.__repr__()
