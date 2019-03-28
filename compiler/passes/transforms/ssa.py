import networkx as nx

from compiler.data_structures.basic_block import BasicBlock
# from compiler.data_structures.ir import IRInstruction
from compiler.data_structures.ir import *
from compiler.data_structures.ir import Phi
from compiler.data_structures.program import Program
from compiler.data_structures.variable import RenamedVar
from .bs_transform import BSTransform


class SSA(BSTransform):

    def __init__(self):
        super().__init__("SSA Transform")
        # The dominance frontier for each function.
        self.frontier = dict()
        # The dominator tree for each function.
        self.dominator_tree = dict()
        # The immediate dominators for each function.
        self.idoms = dict()
        # Bookkeeping for the variable renaming algorithm.
        self.bookkeeper = dict()
        self.program = None

    def transform(self, program: Program):
        self.program = program
        for root in self.program.functions:
            self.log.info("Converting function: {}".format(root))
            self.build_dominators(root)
            self.insert_phi_functions(root)
            self.rename_variables(root)
        return self.program

    def build_dominators(self, root: str):
        """
        This builds the requisite dominator structures:
        dominator tree, immediate dominators, and dominance frontier
        for each function present in the program.
        :param root: Name of function to build for.
        :return: None
        """
        if root == 'foo':
            x = 2
        self.frontier[root] = nx.dominance_frontiers(self.program.bb_graph, self.program.functions[root]['entry'])
        self.idoms[root] = nx.immediate_dominators(self.program.bb_graph, self.program.functions[root]['entry'])
        self.dominator_tree[root] = dict()

        for key, value in self.idoms[root].items():
            if value not in self.dominator_tree[root]:
                self.dominator_tree[root][value] = list()
            # Ensure a self dominated node isn't added
            # This guarantees no infinite iteration
            if key != value:
                self.dominator_tree[root][value].append(key)

    def insert_phi_functions(self, root: str):
        """
        This is the work-list algorithm described in
        Algorithm 19.6 on page 407 of the 2nd edition
        of the Appel book.
        :param root: The function we are looking at.
        :return: None.
        """
        variables = self.program.symbol_table.scope_map[root]
        blocks = self.program.functions[root]['blocks']

        for var_name in variables.get_locals():
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
                if var_name in blocks[block].defs:
                    work_list.append(block)
            while work_list:
                # Grab the next block to look at.
                worker = work_list.pop()
                # Look at the nodes in the frontier of a given worker
                for frontier in self.frontier[root][worker]:
                    # If we haven't inserted a phi node and there are uses
                    # in the frontier, then we must add a phi node to the block.
                    if frontier not in inserted_phi and var_name in blocks[frontier].uses:
                        variable = self.program.symbol_table.scope_map[root].locals[var_name]
                        phi = Phi(variable, [])
                        # There should be one variable
                        # for each in coming edges to the block.
                        for edge in self.program.bb_graph.in_edges(frontier):
                            phi.uses.append(variable)
                        # Insert the phi function.
                        self.program.functions[root]['blocks'][frontier].instructions.insert(0, phi)
                        # Finish the bookkeeping.
                        inserted_phi.add(frontier)
                        if frontier in seen_block:
                            seen_block.remove(frontier)
                            work_list.append(frontier)

    def rename_variables(self, root: str):
        """
        This is the initial set-up and invocation for the recursive
        renaming function call.  It initializes the bookkeeping,
        and then begins renaming variables.
        :param root: The name of the function call to begin the renaming process.
        :return: None
        """
        for variable in self.program.symbol_table.scope_map[root].locals:
            self.bookkeeper[variable] = {'count': 0, 'stack': [0]}
        self.rename(self.program.functions[root]['blocks'][self.program.functions[root]['entry']], root)

    def rename(self, block: BasicBlock, root: str):
        """
        This follows the algorithm described in
        Algorithm 19.7 on page 409 of the 2nd edition
        of the Appel book.
        :param block: The block we are renaming.
        :param root: The function this block resides in.
        :return: None.
        """
        for instruction in block.instructions:
            if instruction.op is not IRInstruction.PHI:
                for x in range(0, len(instruction.uses)):
                    current_var = instruction.uses[x]
                    # We don't care about constants or globals.
                    if not current_var.is_constant and not current_var.is_global:
                        new_name = "{}{}".format(current_var.name,
                                                 self.bookkeeper[current_var.name]['stack'][-1])
                        renamed = RenamedVar(new_name, current_var)
                        instruction.uses[x] = renamed
                        self.program.symbol_table.add_local(renamed, root)
                        if current_var.name in block.uses:
                            block.uses.remove(current_var.name)
                            block.uses.add(renamed.name)
            if instruction.defs:
                version = self.bookkeeper[instruction.defs.name]['count']
                self.bookkeeper[instruction.defs.name]['count'] += 1
                self.bookkeeper[instruction.defs.name]['stack'].append(version)
                original = instruction.defs
                renamed = RenamedVar("{}{}".format(original.name, version), original)
                instruction.defs = renamed
                if not self.program.symbol_table.get_local(renamed, root):
                    self.program.symbol_table.add_local(renamed, root)
                if original.name in block.defs:
                    block.defs.remove(original.name)
                    block.defs.add(renamed.name)
        # Look at the successors of this block
        if block.nid in self.dominator_tree[root]:
            for sid in self.dominator_tree[root][block.nid]:
                successor = self.program.functions[root]['blocks'][sid]
                for instruction in successor.instructions:
                    if instruction.op == IRInstruction.PHI:
                        for x in range(0, len(instruction.uses)):
                            # We don't care about constants or globals.
                            if not instruction.uses[x].is_constant and not instruction.uses[x].is_global:
                                new_var = self.program.symbol_table.get_local(
                                    "{}{}".format(instruction.uses[x].name, x), root)
                                if not new_var:
                                    new_var = RenamedVar("{}{}".format(instruction.uses[x].name, x),
                                                         instruction.uses[x])
                                instruction.uses[x] = new_var
        if block.nid in self.dominator_tree[root]:
            """
            Visit the nodes that are immediately dominated by this.
            """
            for successor in self.dominator_tree[root][block.nid]:
                self.rename(self.program.functions[root]['blocks'][successor], root)
        for instruction in block.instructions:
            # We aren't concerned with instructions that don't have defs
            # Or are constant values.  They don't impact renaming.
            if instruction.op is not IRInstruction.CONSTANT and instruction.defs:
                if self.bookkeeper[instruction.defs.points_to]['stack']:
                    self.bookkeeper[instruction.defs.points_to]['stack'].pop()
