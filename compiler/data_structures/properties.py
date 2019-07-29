from enum import Enum
from enum import IntEnum
from typing import Dict


class BSTime(IntEnum):
    NANOSECOND = 1
    MICROSECOND = 2
    MILLISECOND = 3
    CENTISECOND = 4
    DECISECOND = 5
    SECOND = 6
    MINUTE = 7
    HOUR = 8
    DAY = 9
    WEEK = 10
    MONTH = 11
    YEAR = 12

    def normalize(self, quantity: float):
        if self.value == BSTime.NANOSECOND:
            return quantity / 100000.0
        elif self == BSTime.MICROSECOND:
            return quantity / 10000.0
        elif self == BSTime.MILLISECOND:
            return quantity / 1000.0
        elif self == BSTime.CENTISECOND:
            return quantity / 100.0
        elif self == BSTime.DECISECOND:
            return quantity / 10.0
        elif self == BSTime.SECOND:
            return quantity
        elif self == BSTime.MINUTE:
            return quantity * 60.0
        elif self == BSTime.HOUR:
            return quantity * 60 * 60.0
        elif self == BSTime.DAY:
            return quantity * 60 * 60 * 24.0
        elif self == BSTime.WEEK:
            return quantity * 60 * 60 * 24 * 7.0
        elif self == BSTime.MONTH:
            return quantity * 60 * 60 * 24 * 7 * 30.0
        elif self == BSTime.YEAR:
            return quantity * 60 * 60 * 24 * 365.0
        else:
            return quantity

    @staticmethod
    def get_from_string(time: str):
        if time == "ns":
            return BSTime.NANOSECOND
        elif time == "us":
            return BSTime.MICROSECOND
        elif time == "ms":
            return BSTime.MILLISECOND
        elif time == "cs":
            return BSTime.CENTISECOND
        elif time == "ds":
            return BSTime.DECISECOND
        elif time == "s":
            return BSTime.SECOND
        elif time == "m":
            return BSTime.MINUTE
        elif time == "h":
            return BSTime.HOUR
        elif time == "d":
            return BSTime.DAY
        elif time == "w":
            return BSTime.WEEK
        elif time == "mo":
            return BSTime.MONTH
        elif time == "y":
            return BSTime.YEAR
        else:
            return BSTime.SECOND


class BSTemperature(Enum):
    CELSIUS = 0
    FAHRENHEIT = 1
    KELVIN = 2

    def normalize(self, quantity: float):
        if self == BSTemperature.KELVIN:
            return quantity - 273.15
        elif self == BSTemperature.CELSIUS:
            return quantity
        elif self == BSTemperature.FAHRENHEIT:
            return (quantity - 32) * (5 / 9.0)
        else:
            return quantity

    @staticmethod
    def get_from_string(temp: str):
        if temp == "f":
            return BSTemperature.FAHRENHEIT
        elif temp == "k":
            return BSTemperature.KELVIN
        else:
            return BSTemperature.CELSIUS


class BSVolume(Enum):
    NANOLITRE = -1
    MICROLITRE = 0
    MILLILITRE = 1
    CENTILITRE = 2
    DECILITRE = 4
    LITRE = 8
    DECALITRE = 16

    def normalize(self, quantity: float) -> float:
        """
        Normalize the quantity to be that of
        a microlitre.
        :param quantity: float volume of fluid
        :return: The normalized fluidic volume.
        """
        if self == BSVolume.NANOLITRE:
            return quantity / 10.0
        elif self == BSVolume.MICROLITRE:
            return quantity
        elif self == BSVolume.MILLILITRE:
            return quantity * 10.0
        elif self == BSVolume.CENTILITRE:
            return quantity * 100.0
        elif self == BSVolume.DECILITRE:
            return quantity * 1000.0
        elif self == BSVolume.LITRE:
            return quantity * 10000.0
        elif self == BSVolume.DECALITRE:
            return quantity * 100000.0
        else:
            return quantity

    @staticmethod
    def get_from_string(volume: str):
        if volume == "nL":
            return BSVolume.NANOLITRE
        elif volume == "L":
            return BSVolume.LITRE
        elif volume == "mL":
            return BSVolume.MILLILITRE
        elif volume == "cL":
            return BSVolume.CENTILITRE
        elif volume == "dL":
            return BSVolume.DECILITRE
        elif volume == "daL":
            return BSVolume.DECALITRE
        else:
            return BSVolume.MICROLITRE


class FluidProperties(object):

    def __init__(self, volume: float = 10.0, vol_units: BSVolume = BSVolume.MICROLITRE,
                 temp: float = 23.0, temp_units: BSTemperature = BSTemperature.CELSIUS):
        self._volume = volume
        self._volume_units = vol_units
        self._temperature = temp
        self._temperature_units = temp_units

    @property
    def volume(self):
        return {'quantity': self._volume, 'units': self._volume_units}

    @volume.setter
    def volume(self, vol: Dict):
        """
        Upon entering in here, we can recalculate any other
        members that are dependent upon this property.

        The form of the dict can be in 4 forms:
        "op" can be: {mix | split | use | heat}
        The [index] can only be an int and it *must* reference
        a valid index within the variables value array.
        Mix:
            {'op': 'mix'',
                'values': { [index]: {'input_x': {'quantity': [float], 'units': [BSVolume]}}}}
        Use:
            {'op': 'use', 'values': { [index]: {'quantity': [float], 'units': [BSVolume]}}}

        :param vol: volume attributes.
        :return: None.
        """
        if vol['op'] == 'mix':
            total = 0
            for k, v in vol['values'].items():
                total += v['units'].normalize(v['quantity'])
            self._volume = total
            self._volume_units = BSVolume.MICROLITRE
        elif vol['op'] == 'use':
            self._volume -= vol['values']['units'].normalize(vol['values']['quantity'])

    @property
    def temperature(self):
        return {'quantity': self._temperature, 'units': self._temperature_units}

    @temperature.setter
    def temperature(self, temp: Dict):
        """
        Heat:
            {'op': 'heat', 'values': { [index]: {'quantity': [float], 'units': [BSTemperature]}}}
        :param temp:
        :return:
        """
        self._temperature = temp['values']['units'].normalize(temp['values']['quantity'])
        self._temperature_units = BSTemperature.CELSIUS
