import networkx as nx

from compiler.data_structures.bs_program import BSProgram
from .bs_transform import BSTransform


class SSA(BSTransform):

    def __init__(self):
        super().__init__("SSA Transform")
        self.dominates = dict()
        self.dominated_by = dict()

    def transform(self, program: BSProgram):
        self.log.info("running ssa transformation")
        for root in program.roots:
            self.dominates[root] = nx.dominance_frontiers(program.bb_graph, root)
            self.dominated_by[root] = dict()
            for key, value in self.dominates[root].items():
                for v in value:
                    if v not in self.dominated_by[root]:
                        self.dominated_by[root][v] = set()
                    self.dominated_by[root][v].add(key)

        self.log.info(self.dominates)
        self.log.info(self.dominated_by)

        self.log.info(program.basic_blocks)

        return program
