from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.bs_base_visitor import BSBaseVisitor


class TargetVisitor(BSBaseVisitor):

    def __init__(self, symbol_table: SymbolTable, name: str):
        self.name = name
        self.compiled = ""
        super().__init__(symbol_table)

    def add(self, code: str):
        self.compiled += code + self.nl

    def print_program(self):
        self.log.warning(self.compiled)
