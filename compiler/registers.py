from shared.variable import *


class Register(object):

    def __init__(self, value: Variable):
        self.value = value


class Module(object):
    id_counter = 0

    def __init__(self, value: Variable):
        super().__init__(value)

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Stationary(object):
    id_counter = 0

    def __init__(self, value: Variable):
        super().__init__(value)

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Global(object):
    id_counter = 0

    def __init__(self, value: Variable):
        super().__init__(value)

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Temporary(Register):
    id_counter = 0

    def __init__(self, value: Variable):
        super().__init__(value)

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Output(Register):
    id_counter = 0

    def __init__(self, value: Variable):
        super().__init__(value)

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid
