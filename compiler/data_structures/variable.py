from abc import ABCMeta, abstractmethod
from typing import Set, Dict, Any

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


class Fluid(Variable):

    def __init__(self, name: str, types: Set[ChemTypes] = {ChemTypes.MAT}, scope: str = "main", size: int = 1,
                 volume: float = 10.0, units: BSVolume = BSVolume.MICROLITRE):
        super().__init__(name, types, scope)
        self.ph = -1.0
        self.concentration = -1.0
        self.viscocity = -1.0
        self.density = -1.0
        # Ensure everything is in Microlitres.
        self._value = list()
        for x in range(size):
            self._value.append({'quantity': units.normalize(volume), 'units': BSVolume.MICROLITRE})

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
        for x in self._value:
            if x['units'] != BSVolume.MICROLITRE:
                total += x['units'].normalize(x['quantity'])
            else:
                total += x['quantity']
        return {"quantity": total, "units": BSVolume.MICROLITRE}

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, val: Dict):
        """
        Changes the value of this variable.
        This is where volume, concentration,
        viscocity, density, etc will be
        manipulated. As the volume changes,
        some of the dependent attributes will
        change in suite as well.  This property
        is the place to manage this.

        The form of the dict can be in 3 forms:
        "op" can be: {mix | split | use}
        The [index] can only be an int and it *must* reference
        a valid index within the variables value array.
        Mix:
            {'op': 'mix'', 'values': { [index]: {'input_x': {'quantity': [float], 'units': [BSVolume]}}}}
        Split:
            {'op': 'split', 'values': {'size': [int]}}
        Use:
            {'op': 'use', 'values': { [index]: {'quantity': [float], 'units': [BSVolume]}}}
        :param val: Dict of indexes to use volume.
        :return: None.
        """
        if val['op'] == 'mix':
            # Reset the volume of this droplet.
            for k, v in val['values'].items():
                total = 0
                if v['input_1']['units'] != v['input_2']['units']:
                    total += v['input_1']['units'].normalize(v['input_1']['quantity'])
                    total += v['input_2']['units'].normalize(v['input_2']['quantity'])
                else:
                    total = v['input_1']['quantity'] + v['input_2']['quantity']
                    if v['input_1']['units'] != BSVolume.MICROLITRE:
                        total = v['input_1']['units'].normalize(total)
                self._value[k] = {'quantity': total, 'units': BSVolume.MICROLITRE}
        elif val['op'] == 'split':
            pass
        elif val['op'] == 'use':
            for k, v in val['values'].items():
                if v['units'] == self._value[k]['units']:
                    self._value[k]['quantity'] = self._value[k]['quantity'] - v['quantity']
                else:
                    self._value[k]['quantity'] -= v['units'].normalize(v['quantity'])
            # x = 0
            # while x < len(val['values']):
            #     if val['values'][x]['units'] == self._value[x]['units']:
            #         self._value[x]['quantity'] = self._value[x]['quantity'] - val['values'][x]['quantity']
            #     else:
            #         self._value[x]['quantity'] -= val['values'][x]['units'].normalize(val['values'][x]['quantity'])
            #     x += 1
            # for index in range(len(val['values'])):
            # # for k, v in val['values'].items():
            #     if val['values'][index]['units'] == self._value[index]['units']:
            #         self._value[index]['quantity'] = self._value[index]['quantity'] - val['values'][index]['quantity']
            #     else:
            #         self._value[index]['quantity'] -= val['values'][index]['units'].normalize(val['values'][index]['quantity'])

    def __repr__(self):
        output = "Chemical: "
        output += super().__repr__() + "\t"
        output += "{}".format(self.volume)
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
