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
        self.frontier = defaultdict(lambda: defaultdict(lambda: set()))
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
            self.insert_phi_functions2(root)
            # self.log.debug("Done inserting phi nodes.")
            # self.log.debug("Renaming variables.")
            self.rename_variables(root)

            # self.log.debug("Done renaming variables.")
            # self.log.debug("Removing direct copy phi nodes.")
            self.update_block_def_use(root)
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
                if nid not in self.frontier[root]:
                    nid -= 1
                    continue
                # This is Appel's y \in DF[n]
                for dominator in self.frontier[root][nid]:
                    # This is Appel's a \notin A_{phi}[y]
                    if dominator not in needs_phi and dominator in self.program.functions[root]['blocks']:
                        #added the above check to make sure dominiator is in the blocks so functions can be called muliple times in a bs file
                        phi = Phi(var, [var for x in range(len(self.program.bb_graph.in_edges(dominator)))])
                        self.program.functions[root]['blocks'][dominator].phis.add(phi)
                        self.program.functions[root]['blocks'][dominator].instructions.insert(0, phi)
                        needs_phi.add(dominator)
                    if dominator not in seen_block:
                        work_list.add(dominator)
                        seen_block.add(dominator)

    def insert_phi_functions2(self, root: str):
        """
        Appel alg 19.6
        Step 1:
        for each node n
            for each variable a in Aorig[n]
            defsites[a] ← defsites[a] ∪ {n}
        """
        V = set()
        defsites = defaultdict(lambda: set())
        for nid, block in self.program.functions[root]['blocks'].items():
            for a in block.defs:
                V.add(a)
                defsites[a].add(nid)

        """
        Step 2: the worklist:
        for each variable a
            W ← defsites[a] 
            while W not empty
                remove some node n from W 
                for each y in DF[n]
                    if a ̸∈ Aφ[y]
                        insert the statement a ← φ(a,a,...,a) at the top 
                          of block y, where the φ-function has as many
                          arguments as y has predecessors 
                        Aφ[Y]← Aφ[Y]∪{a}
                    if a ̸∈ Aorig[y]
                        W ← W ∪ {y}
        """
        A_phi = defaultdict(lambda: set())
        for a in V:
            W = defsites[a]
            while W:
                nid = W.pop()
                block = self.program.functions[root]['blocks'][nid]
                if nid not in self.frontier[root]:
                    print("what's pu with this?")
                    continue
                for y in self.frontier[root][nid]:
                    if a not in A_phi[y]:
                        phi = Phi(a, [a for _ in range(len(self.program.bb_graph.in_edges(y)))])
                        self.program.functions[root]['blocks'][y].phis.add(phi)
                        self.program.functions[root]['blocks'][y].instructions.insert(0, phi)
                        A_phi[y].add(a)
                    if a not in block.defs:
                        W.add(y)

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
        if self.program.config.inline:
            if root in self.program.symbol_table.functions:
                return
        instruction = None #added such that instruction can't end up undeclared later
        for instruction in block.instructions:
            if instruction.op != IRInstruction.PHI:
                for x, use in enumerate(instruction.uses):
                    if self.program.symbol_table.is_global(use['name']):
                        continue

                    use_name = use['name']

                    renamed = {'name': use_name + str(self.bookkeeper[use_name]['stack'][-1]),
                               'offset': use['offset'], 'size': use['size'], 'var': None}
                    if use_name in self.program.symbol_table.scope_map[root].locals:
                        location = root
                    else:
                        location = root
                        for area in self.program.symbol_table.scope_map:
                            if use_name in self.program.symbol_table.scope_map[area].locals:
                                location = area
                    renamed_var = RenamedSymbol(renamed['name'],
                                                self.program.symbol_table.get_symbol(use_name, location))
                    self.program.symbol_table.add_local_to_scope(renamed_var, root)
                    renamed['var'] = renamed_var
                    instruction.uses[x] = renamed
                    pass
            if instruction.op in InstructionSet.assignment or instruction.op in InstructionSet.numeric_assignment:
                if instruction.op == IRInstruction.PHI:
                    old = {'name': instruction.defs, 'offset': -1, 'size': -1, 'var': None}
                else:
                    old = instruction.defs

                # count[deff] = count[deff] + 1
                # i = count[deff]
                # stack[deff].push(i)

                old_name = old['name']

                self.bookkeeper[old_name]['count'] += 1
                self.bookkeeper[old_name]['stack'].append(self.bookkeeper[old_name]['count'])

                if 'size' not in old:
                    renamed = {'name': old_name + str(self.bookkeeper[old_name]['stack'][-1]),
                               'offset': old['offset'], 'size': 1, 'var': None}

                else:
                    renamed = {'name': old_name + str(self.bookkeeper[old_name]['stack'][-1]),
                           'offset': old['offset'], 'size': old['size'], 'var': None}
                if old_name in self.program.symbol_table.scope_map[root].locals:
                    location = root
                else:
                    location = root
                    for area in self.program.symbol_table.scope_map:
                        if old_name in self.program.symbol_table.scope_map[area].locals:
                            location = area
                renamed_var = RenamedSymbol(renamed['name'], self.program.symbol_table.get_symbol(old_name, location))
                self.program.symbol_table.add_local_to_scope(renamed_var, root)
                # replace deff with deff_i in instruction
                # preserve volume data if applicable
                if instruction.op in {IRInstruction.DISPENSE, IRInstruction.MIX, IRInstruction.SPLIT, IRInstruction.DISPOSE, IRInstruction.HEAT, IRInstruction.DETECT}:
                    if hasattr(instruction.defs['var'], 'volumes') and hasattr(renamed_var, 'volumes'):
                        renamed_var.volumes = instruction.defs['var'].volumes  # keep passed in volume info
                renamed['var'] = renamed_var
                instruction.defs = renamed
            if instruction.op in {IRInstruction.HEAT, IRInstruction.DISPOSE, IRInstruction.RETURN}:
                '''
                This exists because a heat and dispose don't create new definitions.
                In other words, it doesn't consume any variable, just changes
                an attribute about a material.
                Because of this fact, we set the def to the renamed use. 
                '''
                instruction.defs = instruction.uses[0]
        if instruction is None or instruction.name not in {'RETURN', 'DISPOSE', 'NOP'}: #if last intrustion is return, there is no further nesting

            for j, successor in enumerate(self.program.bb_graph.out_edges(block.nid)):
                '''
                This successor is a successor -- or an outgoing edge within the CFG.
                '''

                if successor[1] not in self.program.functions[root]['blocks']:
                    continue

                else:
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
            if successor == list(self.program.functions[root]['blocks'].keys())[-1] + 1 and instruction.op == IRInstruction.CALL:
                successor = list(self.program.functions[root]['blocks'].keys())[-1]
            if successor in self.program.functions[root]['blocks']:
                self.rename(self.program.functions[root]['blocks'][successor], root)
            else:
                continue
        for instruction in block.instructions:
            if instruction.defs and instruction.op not in {IRInstruction.HEAT, IRInstruction.DISPOSE, IRInstruction.RETURN}:
                # We must use the old points to name
                # because we've lost it at this point.
                self.bookkeeper[instruction.defs['var'].points_to.name]['stack'].pop()

    def update_block_def_use(self, root: str):
        for nid, block in self.program.functions[root]['blocks'].items():
            block.defs = set()
            block.uses = set()
            for instruction in block.instructions:
                if instruction.op in {IRInstruction.PHI}:
                    continue
                for use in instruction.uses:
                    block.uses.add(use['name'])
                if instruction.op in {IRInstruction.HEAT, IRInstruction.DISPOSE, IRInstruction.RETURN}:
                    continue
                if instruction.defs:
                    block.defs.add(instruction.defs['name'])

    def remove_copies(self, root: str):
        # TODO [review]: I'm unconvinced that this does what you think it does, with the current implementation.
        #  It seems either checking for ...uses[0] == ...uses[1] may be the correct check, but there are more issues.
        #  In any case, it may be easier to simply _not insert a PHI node_ if it is a simple copy operation,
        #   rather than trying to remove it later.  This requires not only the removal of the node,
        #   but should also, in the case where the PHI node is the _only_ instruction in the block,
        #   remove the block from the graph, connecting preds with succs.
        for nid, block in self.program.functions[root]['blocks'].items():
            if block.phis:
                x = 0
                while x < len(block.phis):
                    if block.instructions[x].op == IRInstruction.PHI:
                        if len(block.instructions[x].uses) == 2:
                            if block.instructions[x].uses[0] == block.instructions[x].uses[1]:
                                # for use in block.instructions[x].uses:
                                #     if use[-1] == '0':
                                phi = block.instructions[x]
                                block.instructions.pop(x)
                                block.phis.remove(phi)
                                # We subtract one because popping reduces
                                # the size of the array.  This prevents the
                                # case where you pop an instruction and try
                                # to reference an index out of bounds.
                                x -= 1
                    else:
                        break
                    x += 1
