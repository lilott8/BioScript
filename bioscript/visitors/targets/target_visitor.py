from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.bs_base_visitor import BSBaseVisitor


class TargetVisitor(BSBaseVisitor):

    def __init__(self, symbol_table: SymbolTable):
        super().__init__(symbol_table)
