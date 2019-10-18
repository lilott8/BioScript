from collections import defaultdict
from typing import Set

import networkx as nx

from compiler.data_structures.basic_block import BasicBlock
# from compiler.data_structures.ir import IRInstruction
from compiler.data_structures.ir import *
from compiler.data_structures.ir import Phi
from compiler.data_structures.program import Program
from compiler.data_structures.variable import RenamedSymbol
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

    def transform(self, program: Program) -> Program:
        self.program = program
        for root in self.program.functions:
            self.log.info(f"Running SSA on function: {root}")
            self.build_dominators(root)
            self.insert_phi_function_new(root)
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
        self.frontier[root] = nx.dominance_frontiers(self.program.bb_graph, self.program.functions[root]['entry'])
        self.idoms[root] = nx.immediate_dominators(self.program.bb_graph, self.program.functions[root]['entry'])
        self.dominator_tree[root] = defaultdict(lambda: set())

        self.log.warning(self.frontier[root])

        for key, value in self.idoms[root].items():
            # Ensure a self dominated node isn't added
            # This guarantees no infinite iteration
            if key != value:
                self.dominator_tree[root][value].add(key)

    def insert_phi_function_new(self, root: str):
        '''
        You downloaded the book, but it's also here:
        http://ssabook.gforge.inria.fr/latest/book.pdf
        '''
        for name, var in self.program.symbol_table.scope_map[root].locals.items():
            # Set of blocks where phi's are added
            phis = set()
            # The set of basic blocks that contain definitions of a variable
            defs = set()
            # Find all the def sites for the variable
            for bid, block in self.program.functions[root]['blocks'].items():
                if name in block.defs:
                    defs.add(block)
            while defs:
                block = defs.pop()
                for dominator in self.frontier[root][block.nid]:
                    if dominator not in phis:
                        dom_block = self.program.functions[root]['blocks'][dominator]
                        # self.log.error(f"We need to add a phi node for {name} to block {dominator}")
                        # Build a phi node and add a variable for each incoming edge.
                        phi = Phi(name, ['x' for x in range(len(self.program.bb_graph.in_edges(dominator)))])
                        # Prepend the phi node to the top of the block.
                        dom_block.instructions.insert(0, phi)
                        phis.add(dominator)
                        if dominator not in defs:
                            defs.add(self.program.functions[root]['blocks'][dominator])

        self.log.debug("Done inserting phi nodes.")

    def insert_phi_functions(self, root: str):
        """
        This is the work-list algorithm described in
        Algorithm 19.6 on page 407 of the 2nd edition
        of the Appel book.
        :param root: The function we are looking at.
        :return: None.
        """
        self.log.debug("Inserting phi nodes now.")
        variables = self.program.symbol_table.scope_map[root].locals
        blocks = self.program.functions[root]['blocks']

        for var_name, var in variables.items():
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
            self.log.info(work_list)
            while work_list:
                # Grab the next block to look at.
                worker = work_list.pop()
                # Look at the nodes in the frontier of a given worker
                for frontier in self.frontier[root][worker]:
                    self.log.info(f"Frontier: {frontier}\tUses: {blocks[frontier].uses}")
                    self.log.debug(f"{frontier} dominates: {self.frontier[root][frontier]}")
                    # If we haven't inserted a phi node and there are uses
                    # in the frontier, then we must add a phi node to the block.
                    if frontier not in inserted_phi and var_name in blocks[frontier].uses:
                        variable = self.program.symbol_table.get_symbol(var_name, root)
                        phi = Phi(variable.name, [])
                        # There should be one variable
                        # for each in coming edges to the block.
                        for edge in self.program.bb_graph.in_edges(frontier):
                            self.log.error("Adding phi node...")
                            phi.uses.append(variable.name)
                        # Insert the phi function.
                        self.program.functions[root]['blocks'][frontier].instructions.insert(0, phi)
                        # Finish the bookkeeping.
                        inserted_phi.add(frontier)
                        if frontier in seen_block:
                            seen_block.remove(frontier)
                            work_list.append(frontier)

    def generate_name(self, name: str):
        x = self.bookkeeper[name]['count']
        self.bookkeeper[name]['count'] += 1
        self.bookkeeper[name]['stack'].append(x)
        return f"{name}{x}"

    def add_renamed_symbol(self, renamed: str, old: Dict, root: str):
        self.log.info(old)
        self.log.debug(renamed)
        if not self.program.symbol_table.get_symbol(renamed, root):
            symbol = RenamedSymbol(renamed, self.program.symbol_table.get_symbol(old['name'], root))
            self.program.symbol_table.add_local_to_scope(symbol, root)

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
        for variable in self.program.symbol_table.globals:
            self.bookkeeper[variable] = {'count': 0, 'stack': [0]}
        self.new_rename(self.program.functions[root]['blocks'][self.program.functions[root]['entry']], root, set())

    def new_rename(self, block: BasicBlock, root: str, visited: Set):
        # For each phi function and x = y op z.
        for instruction in block.instructions:
            if instruction.op != IRInstruction.PHI:
                for use in instruction.uses:
                    self.log.info(
                        f"{block.label.label} - {instruction.op.name}: Renaming use: {use['name']} -> {use['name']}{self.bookkeeper[use['name']]['stack'][-1]}")
                    # i = top(Stack[x])
                    # replace the use of x with x_i in instruction
                    pass
            if instruction.op in InstructionSet.assignment:
                if instruction.op == IRInstruction.PHI:
                    self.bookkeeper[instruction.defs]['count'] += 1
                    self.bookkeeper[instruction.defs]['stack'].append(self.bookkeeper[instruction.defs]['count'])
                    self.log.info(
                        f"{block.label.label} - {instruction.op.name}: Renaming def: {instruction.defs} -> {instruction.defs}{self.bookkeeper[instruction.defs]['stack'][-1]}")
                else:
                    self.bookkeeper[instruction.defs['name']]['count'] += 1
                    self.bookkeeper[instruction.defs['name']]['stack'].append(
                        self.bookkeeper[instruction.defs['name']]['count'])
                    self.log.info(
                        f"{block.label.label} - {instruction.op.name}: Renaming def: {instruction.defs['name']} -> {instruction.defs['name']}{self.bookkeeper[instruction.defs['name']]['stack'][-1]}")
                # count[deff] = count[deff] + 1
                # i = count[deff]
                # stack[deff].push(i)
                # replace deff with deff_i in instruction
                pass
        for successor in self.dominator_tree[root][block.nid]:
            self.log.debug(successor)
            succ_block = self.program.functions[root]['blocks'][successor]
            for instruction in succ_block.instructions:
                if instruction.op == IRInstruction.PHI:
                    # i = stack[deff].peek()
                    # replace use[i] with use[i]_i
                    self.log.error("Figure out how to map n -> j from appel.")
                    for x, count in enumerate(self.bookkeeper[instruction.defs]['stack']):
                        self.log.info(
                            f"{succ_block.label.label} - {instruction.op.name}: Replacing phi node use {instruction.uses[x]} -> {instruction.uses[x]}{count}")
                    pass
                else:
                    break
        for successor in self.dominator_tree[root][block.nid]:
            self.log.debug(f"Visiting {successor}")
            self.new_rename(self.program.functions[root]['blocks'][successor], root, visited)
        visited.add(block.nid)
        for deff in block.defs:
            self.bookkeeper[deff]['stack'].pop()

    def rename2(self, block: BasicBlock, root: str, visited: Set):
        if block.nid in visited:
            return
        for instruction in block.instructions:
            if instruction.op == IRInstruction.PHI:
                # GenName(LHS(p)) and replace v with v_i, where i=Top(Stack[v])
                deff = instruction.defs
                renamed = self.generate_name(deff)
                self.log.warn("The dictionary is not being updated correctly.")
                instruction.defs = {'name': renamed, 'offset': -1, 'size': -1}
                self.add_renamed_symbol(renamed, {'name': deff}, root)
        for instruction in block.instructions:
            if instruction.op != IRInstruction.PHI:
                if instruction.defs:
                    old = instruction.defs
                    self.log.error(instruction.defs)
                    # replace var by var_i where i = Top(Stacks[var])
                    renamed = self.generate_name(instruction.defs['name'])
                    self.log.info("The dictionary is not being updated correctly.")
                    instruction.defs = {'name': renamed, 'offset': instruction.defs['offset'], 'size': -1,
                                        'var': old['var']}
                    self.add_renamed_symbol(renamed, old, root)
                if instruction.uses:
                    for var in instruction.uses:
                        if not self.program.symbol_table.is_global(var['name']):
                            renamed = f"{var['name']}{self.bookkeeper[var['name']]['stack'][-1]}"
                            self.log.info("The dictionary is not being updated correctly.")
                            self.add_renamed_symbol(renamed, var, root)
                            # GenName(var) and replace var with var_i, where i=Top(Stack[var])

                            pass
        for successor in nx.neighbors(self.program.bb_graph, block.nid):
            # j = position in successor's phi-function corresponding to block.nid
            for instruction in self.program.functions[root]['blocks'][successor].instructions:
                if instruction.op == IRInstruction.PHI:
                    self.log.critical(instruction.defs)
                    instruction.defs = f"{instruction.defs}{self.bookkeeper[instruction.defs]['stack'][-1]}"
                    # replace the jth operand of instruction.uses by v_i, where i = Top(Stack[use])
        if block.nid in self.dominator_tree[root]:
            for child in self.dominator_tree[root][block.nid]:
                self.new_rename(self.program.functions[root]['blocks'][child], root, visited)
        # We can mark this as visited now.
        visited.add(block.nid)
        for instruction in block.instructions:
            # We aren't concerned with instructions that don't have defs
            # Or are constant values.  They don't impact renaming.
            if instruction.op is not IRInstruction.CONSTANT and instruction.op is not IRInstruction.JUMP and \
                    instruction.defs:
                var = self.program.symbol_table.get_symbol(instruction.defs['name'], root)
                if self.bookkeeper[var.points_to.name]['stack']:
                    self.bookkeeper[var.points_to.name]['stack'].pop()

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
            if instruction.op is not IRInstruction.PHI and instruction.op is not IRInstruction.JUMP:
                for x in range(0, len(instruction.uses)):
                    current_var = instruction.uses[x]
                    var = self.program.symbol_table.get_symbol(current_var['name'], root)
                    # We don't care about constants or globals.
                    if not self.program.symbol_table.is_global(var.name):
                        new_name = f"{current_var['name']}{self.bookkeeper[current_var['name']]['stack'][-1]}"
                        renamed = RenamedSymbol(new_name, var)
                        instruction.uses[x]['name'] = renamed.name
                        self.program.symbol_table.add_local_to_scope(renamed, root)
                        if current_var['name'] in block.uses:
                            block.uses.remove(current_var['name'])
                            block.uses.add(renamed['name'])
            if instruction.op is not IRInstruction.JUMP and instruction.defs:
                self.log.info(instruction.defs)
                self.log.info(self.bookkeeper)
                version = self.bookkeeper[instruction.defs['name']]['count']
                self.bookkeeper[instruction.defs['name']]['count'] += 1
                self.bookkeeper[instruction.defs['name']]['stack'].append(version)
                original = instruction.defs
                original_var = self.program.symbol_table.get_symbol(original['name'], root)
                self.log.info(original)
                renamed = RenamedSymbol(f"{original['name']}{version}", original_var)
                instruction.defs['name'] = renamed.name
                if not self.program.symbol_table.get_symbol(renamed.name, root):
                    self.program.symbol_table.add_local_to_scope(renamed, root)
                if original['name'] in block.defs:
                    block.defs.remove(original['name'])
                    block.defs.add(renamed.name)
        '''
        Look at the successors of this block from the CFG
        '''
        for sid in nx.neighbors(self.program.bb_graph, block.nid):
            successor = self.program.functions[root]['blocks'][sid]
            for instruction in successor.instructions:
                if instruction.op == IRInstruction.PHI:
                    for x in range(0, len(instruction.uses)):
                        # We don't care about constants or globals.
                        self.log.info(instruction.uses[x])
                        if not self.program.symbol_table.is_global(instruction.uses[x]):
                            new_var = self.program.symbol_table.get_symbol(
                                "{}{}".format(instruction.uses[x], x), root)
                            if not new_var:
                                old_var = self.program.symbol_table.get_symbol(instruction.uses[x], root)
                                self.log.info(old_var)
                                new_var = RenamedSymbol("{}{}".format(instruction.uses[x], x), old_var)
                            instruction.uses[x] = new_var
        '''
        Visit the nodes that are immediately dominated by this.
        This is not successors, it's from the dominator tree:
        https://www.cs.colostate.edu/~mstrout/CS553Fall06/slides/lecture18-SSAusage.pdf
        '''
        for successor in self.dominator_tree[root][block.nid]:
            self.rename(self.program.functions[root]['blocks'][successor], root)
        for instruction in block.instructions:
            # We aren't concerned with instructions that don't have defs
            # Or are constant values.  They don't impact renaming.
            if instruction.op is not IRInstruction.CONSTANT and \
                    instruction.op is not IRInstruction.JUMP and \
                    instruction.defs:
                if self.bookkeeper[instruction.defs.points_to]['stack']:
                    self.bookkeeper[instruction.defs.points_to]['stack'].pop()
