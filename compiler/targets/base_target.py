import colorlog

import config.config
from compiler.data_structures.symbol_table import SymbolTable


class BaseTarget(object):

    def __init__(self, symbol_table: SymbolTable, ir: dict, name="BaseTarget"):
        self.config = config.Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.symbol_table = symbol_table
        self.name = name
        self.program = ""
        self.ir = ir

    def map_mix(self):
        raise NotImplemented

    def map_split(self):
        raise NotImplemented

    def map_detect(self):
        raise NotImplemented

    def map_dispose(self):
        raise NotImplemented

    def map_dispense(self):
        raise NotImplemented

    def map_expression(self):
        raise NotImplemented

    def map_branch(self):
        raise NotImplemented
