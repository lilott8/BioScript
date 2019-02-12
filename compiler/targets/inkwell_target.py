from compiler.symbol_table.symbol_table import SymbolTable
from compiler.targets.base_target import BaseTarget


class InkwellTarget(BaseTarget):

    def __init__(self, symbol_table: SymbolTable, basic_blocks):
        super().__init__(symbol_table, "InkwellTarget")
        self.bb = basic_blocks
