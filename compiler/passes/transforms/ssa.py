import networkx as nx

from compiler.data_structures.program import Program
from .bs_transform import BSTransform


class SSA(BSTransform):

    def __init__(self):
        super().__init__("SSA Transform")
        self.dominates = dict()
        self.dominated_by = dict()
        self.dominator_tree = dict()

    def build_dominator_tree(self, program):
        dominator = None
        for root in program.functions:
            dominator_set = nx.immediate_dominators(program.bb_graph, program.functions[root]['entry'])
            self.dominator_tree[root] = nx.DiGraph()
            for bid in dominator_set:
                # self.dominator_tree[root].add_node()
                self.log.warn(bid)

    def transform(self, program: Program):
        self.build_dominator_tree(program)

        # Build the dominator tree
        dominator_tree = dict()
        for root in program.functions:
            self.log.info(root)
            dominator_tree[root] = nx.immediate_dominators(program.bb_graph, program.functions[root]['entry'])
        self.log.info(dominator_tree)

        """
        To place phi nodes.
        http://www.eecs.umich.edu/courses/eecs583/slides/Lecture8.pdf
        """
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

        # self.log.info(program.basic_blocks)

        return program
