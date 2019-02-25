import colorlog

from compiler.symbol_table.symbol_table import SymbolTable
from config.config import Config


class PassManager(object):

    def __init__(self, symbol_table: SymbolTable, ir: dict):
        self.config = Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.debug("Initializing pass manager.")
        self.ir = ir
        self.symbol_table = symbol_table

    def optimize(self):
        pass
