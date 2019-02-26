import colorlog
import networkx as nx

from compiler.data_structures.symbol_table import SymbolTable


class PhiInserter(object):

    def __init__(self, symbol_table: SymbolTable, ir: dict):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.symbol_table = symbol_table
        self.ir = ir
        self.cfg = ir["cfg"]
        self.basic_blocks = ir['basic_blocks']
        self.globals = ir['globals']
        self.functions = ir['functions']

    def insert_phi_nodes(self):
        dominance = nx.dominance_frontiers(self.cfg, 1)
        self.log.info(dominance)
        self.log.info(self.basic_blocks)
