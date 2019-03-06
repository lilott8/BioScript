from compiler.data_structures.variable import *


class Register(object):

    def __init__(self, value: Variable, rid: int):
        self.value = value
        self.rid = rid

    def __str__(self):
        return "ID: {}\tStoring: {}".format(self.rid, self.value.name)

    def __repr__(self):
        return self.__str__()


class Module(Register):
    id_counter = 1

    def __init__(self, value: Variable):
        super().__init__(value, Module.get_output_id())

    def __str__(self):
        return "[Module]:\t" + super().__str__() + "\n"

    def __repr__(self):
        return self.__str__()

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Stationary(Register):
    id_counter = 1

    def __init__(self, value: Variable):
        super().__init__(value, Stationary.get_output_id())

    def __str__(self):
        return "[Stationary]:\t" + super().__str__() + "\n"

    def __repr__(self):
        return self.__str__()

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Global(Register):
    id_counter = 1

    def __init__(self, value: Variable):
        super().__init__(value, Global.get_output_id())

    def __str__(self):
        return "[Global]:\t" + super().__str__() + "\n"

    def __repr__(self):
        return self.__str__()

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Temporary(Register):
    id_counter = 1

    def __init__(self, value: Variable):
        super().__init__(value, Temporary.get_output_id())

    def __str__(self):
        return "[Temporary]:\t" + super().__str__() + "\n"

    def __repr__(self):
        return self.__str__()

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid


class Output(Register):
    id_counter = 1

    def __init__(self, value: Variable):
        super().__init__(value, Output.get_output_id())

    def __str__(self):
        return "[Output]:\t" + super().__str__() + "\n"

    def __repr__(self):
        return self.__str__()

    @staticmethod
    def get_output_id():
        tid = Output.id_counter
        Output.id_counter += Output.id_counter
        return tid
