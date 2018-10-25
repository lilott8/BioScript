from shared.enums.bs_properties import *
from shared.variable import Variable


class MFSimVarBuilder(object):

    @staticmethod
    def build_global_variable(vid: str, name: str, vtype: str = "CHEMICAL") -> dict:
        output = dict()
        output['VARIABLE_DECLARATION'] = {'ID': vid, 'NAME': name, 'TYPE': vtype}
        return output

    @staticmethod
    def build_sensor_variable(vid: str, name: str, vtype: str = "SENSOR") -> dict:
        output = dict()
        output['SENSOR_DECLARATION'] = {'ID': vid, 'NAME': name, 'TYPE': vtype}
        return output

    @staticmethod
    def build_heat_input(var: Variable) -> dict:
        return MFSimVarBuilder.build_general_input(var)

    @staticmethod
    def build_detect_input(var: Variable) -> dict:
        output = dict()
        output['INPUT_TYPE'] = 'VARIABLE'
        output['VARIABLE'] = {'NAME': var.name}
        return output

    @staticmethod
    def build_variable_declaration(vid: str, name: str, vtype: str = "VARIABLE"):
        output = dict()
        output['VARIABLE_DECLARATION'] = {'ID': vid, 'NAME': name, 'TYPE': vtype}
        return output

    @staticmethod
    def build_mix_input(var: Variable) -> dict:
        return MFSimVarBuilder.build_general_input(var)

    @staticmethod
    def build_general_input(var: Variable) -> dict:
        output = dict()
        output['INPUT_TYPE'] = 'VARIABLE'
        output['VARIABLE'] = {'NAME': var.name}
        return output

    @staticmethod
    def build_input_with_volume(var: Variable, prop: dict):
        output = MFSimVarBuilder.build_general_input(var)
        output['VARIABLE']['VOLUME'] = {'VALUE': prop['quantity'], 'UNITS': prop['units'].name}
        return output

    @staticmethod
    def build_stationary_input(var: Variable):
        output = dict()
        output['INPUT_TYPE'] = 'VARIABLE'
        output['STATIONARY'] = {'NAME': var.name}
        return output

    @staticmethod
    def build_time_property(quantity: int = 10, units: BSTime = BSTime.SECOND) -> dict:
        return MFSimVarBuilder.build_property(quantity, units, 'TIME')

    @staticmethod
    def build_volume_property(quantity: int = 10, units: BSVolume = BSVolume.MICROLITRE) -> dict:
        return MFSimVarBuilder.build_property(quantity, units, 'VOLUME')

    @staticmethod
    def build_temperature_property(quantity: int = 10, units: BSTemperature = BSTemperature.CELSIUS) -> dict:
        return MFSimVarBuilder.build_property(quantity, units, 'TEMPERATURE')

    @staticmethod
    def build_property(quantity: int, units, prop_type) -> dict:
        output = dict()
        output['INPUT_TYPE'] = 'PROPERTY'
        output['PROPERTY'] = {prop_type: {'VALUE': quantity, 'UNITS': units.name}}
        return output

    @staticmethod
    def build_operation(name: str, iid: str, classification: str, inputs: list = list, outputs: list = list) -> dict:
        output = dict()
        output['OPERATION'] = {'NAME': name, 'ID': iid, 'CLASSIFICATION': classification, 'INPUTS': [], 'OUTPUTS': []}

        for x in inputs:
            output['OPERATION']['INPUTS'].append(x)

        for x in outputs:
            output['OPERATION']['OUTPUTS'].append(x)

        return output

    @staticmethod
    def build_detect_output(vid: str, name: str, vtype: str = "SENSOR"):
        output = dict()
        output['SENSOR_DECLARATION'] = {'ID': vid, 'NAME': name, 'TYPE': vtype}
        return output

    @staticmethod
    def build_output(vid: str, name: str, vtype: str = "CHEMICAL"):
        output = dict()
        output['VARIABLE'] = {'ID': vid, 'NAME': name, 'TYPE': vtype}
        return output
