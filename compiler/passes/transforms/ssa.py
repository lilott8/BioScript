import networkx as nx

from compiler.data_structures.ir import Phi
from compiler.data_structures.program import Program
from .bs_transform import BSTransform


class SSA(BSTransform):

    def __init__(self):
        super().__init__("SSA Transform")
        # The dominance frontier for each function.
        self.frontier = dict()
        # The dominator tree for each function.
        self.dominator_tree = dict()
        # The immediate dominators for each function
        self.idoms = dict()
        self.program = None

    def transform(self, program: Program):
        self.program = program
        self.insert_phi_functions()
        # self.rename_variables()
        return self.program

    def insert_phi_functions(self):
        for root in self.program.functions:
            variables = self.program.symbol_table.scope_map[root]
            blocks = self.program.functions[root]['blocks']

            # Save this just to be sure.
            self.frontier[root] = nx.dominance_frontiers(self.program.bb_graph, self.program.functions[root]['entry'])
            self.idoms[root] = nx.immediate_dominators(self.program.bb_graph, self.program.functions[root]['entry'])
            self.dominator_tree[root] = self.compute_dominator_tree(
                self.program.bb_graph, self.program.functions[root]['entry'])

            """
            This algorithm is derived from:
            http://pages.cs.wisc.edu/~fischer/cs701.f08/lectures/Lecture23.4up.pdf
            """
            for variable in variables.get_locals():
                inserted_phi = set()
                # This works in reverse,
                # if a block is in this set,
                # we haven't seen it.
                seen_block = set()
                work_list = list()
                for block in blocks:
                    # Initialize each block as unseen.
                    seen_block.add(block)
                    # If the variable is defined in a block, save it.
                    if variable in blocks[block].defs:
                        work_list.append(block)
                while work_list:
                    # Grab the next block to look at.
                    worker = work_list.pop()
                    # Look at the nodes in the frontier of a given worker
                    for frontier in self.frontier[root][worker]:
                        # If we haven't inserted a phi node and there are uses
                        # in the frontier, then we must add a phi node to the block.
                        if frontier not in inserted_phi and variable in blocks[frontier].uses:
                            phi = Phi(variable, [])
                            # There should be one variable
                            # for each in coming edges to the block.
                            for edge in self.program.bb_graph.in_edges(frontier):
                                phi.phi.append(variable)
                            # Insert the phi function.
                            self.program.functions[root]['blocks'][frontier].instructions.insert(0, phi)
                            # Finish the bookkeeping.
                            inserted_phi.add(frontier)
                            if frontier in seen_block:
                                seen_block.remove(frontier)
                                work_list.append(frontier)

    def rename_variables(self):
        for root in self.program.functions:
            variables = self.program.symbol_table.scope_map[root]

            bookkeeper = dict()

            for variable in variables:
                bookkeeper[variable]['count'] = 0
                bookkeeper[variable]['stack'] = list()
                bookkeeper[variable]['stack'].push(0)

    def compute_dominator_tree(self, graph, entry: int):
        # depth first spanning tree: https://web.cs.wpi.edu/~kal/PLT/PLT8.6.5.html
        return -1
