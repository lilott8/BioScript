import copy
from collections import defaultdict

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
        self.log.debug(f"Beginning SSA conversion for: {self.program.name}")
        for root in self.program.functions:
            self.build_dominators(root)
            # self.log.debug("Inserting phi nodes.")
            self.insert_phi_functions(root)
            # self.log.debug("Done inserting phi nodes.")
            # self.log.debug("Renaming variables.")
            self.rename_variables(root)
            # self.log.debug("Done renaming variables.")
            # self.log.debug("Removing direct copy phi nodes.")
            self.remove_copies(root)
            # self.log.debug("Done removing blind copies.")
        self.log.debug(f"Done converting {self.program.name} to SSA form.")
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

        for key, value in self.idoms[root].items():
            # Ensure a self dominated node isn't added
            # This guarantees no infinite iteration
            if key != value:
                self.dominator_tree[root][value].add(key)

    def insert_phi_functions(self, root: str):
        """
        This is the work-list algorithm described in
        Algorithm 19.6 on page 407 of the 2nd edition
        of the Appel book.
        :param root: The function we are looking at.
        :return: None.
        """
        blocks = self.program.functions[root]['blocks']
        # Maps variable to the blocks that define it.
        # This is Appel's A_{orig}[n]
        def_sites = defaultdict(lambda: set())

        for nid, block in blocks.items():
            for deff in block.defs:
                def_sites[deff].add(nid)
        # var is Appel's a
        for var, sites in def_sites.items():
            # This is Appel's A_{phi}[n]
            needs_phi = set()
            seen_block = set()
            work_list = copy.deepcopy(sites)
            # this is Appel's W
            while work_list:
                # This is Appel's n
                nid = work_list.pop()
                # This is Appel's y \in DF[n]
                for dominator in self.frontier[root][nid]:
                    # This is Appel's a \notin A_{phi}[y]
                    if dominator not in needs_phi:
                        phi = Phi(var, [var for x in range(len(self.program.bb_graph.in_edges(dominator)))])
                        self.program.functions[root]['blocks'][dominator].phis.add(phi)
                        self.program.functions[root]['blocks'][dominator].instructions.insert(0, phi)
                        needs_phi.add(dominator)
                    if dominator not in seen_block:
                        work_list.add(dominator)
                        seen_block.add(dominator)

    def rename_variables(self, root: str):
        """
        This is the initial set-up and invocation for the recursive
        renaming function call.  It initializes the bookkeeping,
        and then begins renaming variables.
        :param root: The name of the function call to begin the renaming process.
        :return: None
        """
        for variable in self.program.symbol_table.scope_map[root].locals:
            self.bookkeeper[variable] = {'count': 0, 'stack': [0], 'renamed': defaultdict(lambda: 0)}
        # for variable in self.program.symbol_table.globals:
        #     self.bookkeeper[variable] = {'count': 0, 'stack': [0]}
        self.rename(self.program.functions[root]['blocks'][self.program.functions[root]['entry']], root)

    def rename(self, block: BasicBlock, root: str):
        """
        This variable renaming algorithm is taken from Appel's Tiger book.
        :param block: block that needs renaming.
        :param root: function name we are in.
        :return: None
        """
        # For each phi function and x = y op z.
        for instruction in block.instructions:
            if instruction.op != IRInstruction.PHI:
                for x, use in enumerate(instruction.uses):
                    if self.program.symbol_table.is_global(use['name']):
                        continue
                    renamed = {'name': use['name'] + str(self.bookkeeper[use['name']]['stack'][-1]),
                               'offset': use['offset'], 'size': use['size'], 'var': None}
                    renamed_var = RenamedSymbol(renamed['name'],
                                                self.program.symbol_table.get_symbol(use['name'], root))
                    self.program.symbol_table.add_local_to_scope(renamed_var, root)
                    renamed['var'] = renamed_var
                    instruction.uses[x] = renamed
                    pass
            if instruction.op in InstructionSet.assignment:
                if instruction.op == IRInstruction.PHI:
                    old = {'name': instruction.defs, 'offset': -1, 'size': -1, 'var': None}
                else:
                    old = instruction.defs

                # count[deff] = count[deff] + 1
                # i = count[deff]
                # stack[deff].push(i)
                self.bookkeeper[old['name']]['count'] += 1
                self.bookkeeper[old['name']]['stack'].append(self.bookkeeper[old['name']]['count'])

                renamed = {'name': old['name'] + str(self.bookkeeper[old['name']]['stack'][-1]),
                           'offset': old['offset'], 'size': old['size'], 'var': None}
                renamed_var = RenamedSymbol(renamed['name'], self.program.symbol_table.get_symbol(old['name'], root))
                self.program.symbol_table.add_local_to_scope(renamed_var, root)
                # replace deff with deff_i in instruction
                renamed['var'] = renamed_var
                instruction.defs = renamed
            if instruction.op in {IRInstruction.HEAT, IRInstruction.DISPOSE}:
                '''
                This exists because a heat and dispose don't create new definitions.
                In other words, it doesn't consume any variable, just changes
                an attribute about a material.
                Because of this fact, we set the def to the renamed use. 
                '''
                instruction.defs = instruction.uses[0]
        for j, successor in enumerate(self.program.bb_graph.out_edges(block.nid)):
            '''
            This successor is a successor -- or an outgoing edge within the CFG. 
            '''
            succ_block = self.program.functions[root]['blocks'][successor[1]]
            # We only care about the PHI nodes of this block
            for instruction in list(filter(lambda instr: instr.op == IRInstruction.PHI, succ_block.instructions)):
                if isinstance(instruction.defs, dict):
                    original_var = instruction.defs['var'].points_to.name
                else:
                    original_var = instruction.defs
                use_count = len(instruction.uses)
                # i = stack[deff].peek()
                # replace use[i] with use[i]_i
                # If the variable has been replaced already,
                # we don't need to look at this phi node.
                if self.bookkeeper[original_var]['renamed'][instruction.iid] < use_count:
                    next_id = self.bookkeeper[original_var]['renamed'][instruction.iid]
                    instruction.uses[next_id] = f"{original_var}{self.bookkeeper[original_var]['stack'][-1]}"
                    self.bookkeeper[original_var]['renamed'][instruction.iid] += 1
        for successor in self.dominator_tree[root][block.nid]:
            '''
            This is a child -- or an outgoing edge within the dominator tree.
            '''
            self.rename(self.program.functions[root]['blocks'][successor], root)
        for instruction in block.instructions:
            if instruction.defs and instruction.op != IRInstruction.HEAT:
                # We must use the old points to name
                # because we've lost it at this point.
                self.bookkeeper[instruction.defs['var'].points_to.name]['stack'].pop()

    def remove_copies(self, root: str):
        for nid, block in self.program.functions[root]['blocks'].items():
            if block.phis:
                x = 0
                while x < len(block.phis):
                    if block.instructions[x].op == IRInstruction.PHI:
                        if len(block.instructions[x].uses) == 2:
                            for use in block.instructions[x].uses:
                                if use[-1] == '0':
                                    block.instructions.pop(x)
                                    # We subtract one because popping reduces
                                    # the size of the array.  This prevents the
                                    # case where you pop an instruction and try
                                    # to reference an index out of bounds.
                                    x -= 1
                    else:
                        break
                    x += 1
