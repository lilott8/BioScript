import networkx as nx

from compiler.data_structures.program import Program
from .bs_transform import BSTransform


class SSA(BSTransform):

    def __init__(self):
        super().__init__("SSA Transform")
        self.dominates = dict()
        self.dominated_by = dict()
        self.program = None

    def transform(self, program: Program):
        self.program = program

        # Build the dominator tree
        dominator_tree = dict()
        for root in program.functions:
            # self.log.info(root)
            dominator_tree[root] = nx.immediate_dominators(program.bb_graph, program.functions[root]['entry'])
        # self.log.info(dominator_tree)

        """
        To place phi nodes.
        http://www.eecs.umich.edu/courses/eecs583/slides/Lecture8.pdf
        """
        for root in program.functions:
            entry = program.functions[root]['entry']
            self.dominates[root] = nx.dominance_frontiers(program.bb_graph, entry)
            self.dominated_by[root] = dict()
            for key, value in self.dominates[root].items():
                for v in value:
                    """
                    This flips the dominance frontier such that what
                    was a key now becomes a value.  So we can see what
                    nodes share a join node and insert a phi node if
                    necessary.
                    """
                    if v not in self.dominated_by[root]:
                        self.dominated_by[root][v] = set()
                    self.dominated_by[root][v].add(key)

                for frontier in self.dominated_by[root]:
                    if len(self.dominated_by[root][frontier]) >= 2:
                        self.insert_phi(frontier, self.dominated_by[root][frontier], key, root)
                    # initial = self.dominated_by[root].pop()
                    # for sets in self.dominated_by[root][frontier]:
                    #     initial = initial.intersection(sets)
                    # self.log.info(initial)

        # self.log.info(self.dominates)
        # self.log.info(self.dominated_by)

        # self.log.info(program.basic_blocks)

        return program

    def insert_phi(self, join, dominates, root, func):
        """
        This inserts phi nodes into the necessary basic blocks.
        :param join: The nodes in dominates that end here.
        :param dominates: The nodes that dominate join.
        :param root: Reference to which function to modify.
        :param func: Function name that is being modified.
        :return:
        """
        self.log.info(func)
        # self.log.info(self.program.functions[func])
        # self.log.info(self.program.functions[func]['blocks'])
        seed = self.program.functions[func]['blocks'][dominates.pop()].defs
        self.log.info(seed)
        for dom in dominates:
            declares = self.program.functions[func]['blocks'][dom].defs
            # pass
        # self.log.info(join).
        # self.log.info(dominates)
        # self.log.info(root)
        pass
