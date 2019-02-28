import networkx as nx

from compiler.data_structures.bs_program import BSProgram
from .bs_transform import BSTransform


class SSA(BSTransform):

    def __init__(self):
        super().__init__("SSA Transform")

    def transform(self, program: BSProgram):
        self.log.info("running ssa transformation")
        dominators = dict()
        for root in program.roots:
            dominators[root] = nx.dominance_frontiers(program.bb_graph, root)
        self.log.info(dominators)
        return program
