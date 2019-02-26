from compiler.data_structures.symbol_table import SymbolTable
from compiler.targets.base_target import BaseTarget


class PuddleTarget(BaseTarget):

    def __init__(self, symbol_table: SymbolTable, ir: dict):
        super().__init__(symbol_table, ir, "PuddleTarget")
