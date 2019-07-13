from compiler.targets.base_target import BaseTarget
from compiler.data_structures import IRInstruction
from compiler.data_structures.ir import Conditional
from compiler.data_structures import RenamedVar
from compiler.data_structures import RelationalOps
from collections import deque
import networkx as nx


class TransferNode:

    def __init__(self, tid, bid, name, ttype):
        self.tid = tid
        self.iid = tid
        self.name = name
        self.bid = bid
        self.type = ttype


class MFSimTarget(BaseTarget):

    def __init__(self, program):
        super().__init__(program, "MFSimTarget")
        self.cblock = None
        self.opid = None
        self.root = None
        self.cgid = 0
        self.expid = 0
        self.cfg = dict()
        self.block_transfers = dict()
        self.loop_headers = dict()
        # start transfer nodes from id 100.
        self.log.warn("Statically starting transfer IDs from 100. This could be an issue for very large assays.")
        self.tid = 100

    def build_cfg(self):
        for root in self.program.functions:
            leafs = set()
            tags = dict()
            self.dags[root] = dict()
            self.cfg['graph'] = nx.DiGraph()
            remove_nodes = set()
            remove_edges_from = set()
            for bid, block in self.program.functions[root]['blocks'].items():
                if not block.instructions:
                    # attach edges from pred to succ
                    for pid in self.program.functions[root]['graph'].predecessors(bid):
                        for sid in self.program.functions[root]['graph'].successors(bid):
                            self.cfg['graph'].add_edge(pid, sid)
                    # add bid to the list of nodes that must have all edges removed from final graph
                    remove_nodes.add(bid)
                    continue
                for sid in self.program.functions[root]['graph'].successors(bid):
                    self.cfg['graph'].add_edge(bid, sid)
                self.cfg[bid] = dict()
                curr = self.cfg[bid]
                write = True
                dag = nx.DiGraph()
                for instruction in block.instructions:
                    # self.log.info(instruction)

                    # deal with conditionals
                    if instruction.op is IRInstruction.CONDITIONAL:

                        if len(block.instructions) is 1:
                            write = False

                        true_label = instruction.true_branch.label
                        false_label = instruction.false_branch.label

                        true_block = None
                        false_block = None

                        for bbid, bblock in self.program.functions[root]['blocks'].items():
                            if bblock.instructions and bblock.label:
                                if bblock.label.label is true_label:
                                    true_block = bbid
                                elif bblock.label.label is false_label:
                                    false_block = bbid
                                continue

                        if instruction.cond_type in ['repeat', 'while']:
                            if bid in self.loop_headers:
                                self.loop_headers[bid].add({'instr': instruction, 't': true_block, 'f': false_block})
                            else:
                                self.loop_headers[bid] = {'instr': instruction, 't': true_block, 'f': false_block}

                        curr[instruction.iid] = dict()
                        curr[instruction.iid] = {'instr': instruction, 'f': false_block,
                                                 't': true_block}
                        if instruction.left.name.startswith("REPEAT"):
                            curr[instruction.iid]['c'] = 'repeat'
                            curr[instruction.iid]['repeat'] = instruction.left.value
                        else:  # could be nested conditional
                            curr[instruction.iid]['c'] = instruction.relop
                            self.log.warn("TEST non-repeat CONDITIONALS")
                    #  non-conditionals
                    elif hasattr(instruction, 'uses'):
                        # Case x = op y (dispense, heat, dispose, store)
                        if len(instruction.uses) == 1:
                            # Look at the r-value.
                            use = next(iter(instruction.uses))
                            if use not in leafs:
                                dag.add_node(use.name, type="variable")
                                leafs.add(use.name)
                                leaf = use.name
                            else:
                                leaf = use.name
                            # Do the same thing, except for the l-value.
                            if instruction.defs:
                                if instruction.defs.name not in tags:
                                    dag.add_node(leaf, iid=instruction.iid, op=instruction.op.name, type="register")
                                    var_def = instruction.defs.name
                                    tags[instruction.defs.name] = var_def
                                else:
                                    var_def = instruction.defs.name
                                dag.add_edge(leaf, var_def)
                        else:
                            # Case x = y op z (mix, split, arithmetic)
                            var_def = instruction.defs.name
                            dag.add_node(var_def, iid=instruction.iid, op=instruction.op.name, type="register")
                            tags[var_def] = var_def
                            for use in instruction.uses:
                                leaf = use.name
                                if leaf not in leafs:
                                    dag.add_node(leaf, type="variable")
                                    leafs.add(leaf)
                                dag.add_edge(leaf, var_def)

                    # if a material is disposed, it should not define a new material for later use
                    if instruction.op is IRInstruction.DISPOSE:
                        defined = instruction.defs.name
                        instruction.defs = None
                        block.defs.remove(defined)
                        # in the case where the only def in a block has been removed because it was a dipose,
                        #   we do not need any outgoing edges.
                        # TODO: test case: transfer_in A, B; dispose A (do nothing with B).
                        #   if this fails, we could explicitly add a def to the block for transfer_ins prior to
                        #   running these checks (in transform())
                        if len(block.defs) is 0:
                            remove_edges_from.add(bid)

                if write:
                    self.program.functions[root]['blocks'][bid].dag = dag
                    self.dags[root][bid] = dag

            for remove in remove_nodes:
                if remove in self.cfg['graph'].nodes:
                    self.cfg['graph'].remove_node(remove)

            for remove in remove_edges_from:
                succ = list(self.cfg['graph'].successors(remove))
                for s in succ:
                    self.cfg['graph'].remove_edge(remove, s)


        return False

    @staticmethod
    def write_transfer(id, name, out=False) -> str:
        return "NODE (%s, %s, %s)\n" % (str(id), "TRANSFER_OUT" if out else "TRANSFER_IN", name)

    def write_edge(self, _from, _to) -> str:
        # should not be trying to write an edge
        if self.cblock.dag is None:
            self.log.warn("write edge returning without writing an edge")
            pass
        return "EDGE (%s, %s)\n" % (_from, _to)

    """
        An MFSim MIX node has 5 parameters:
          nodeid, "MIX", number of input drops, time, mixName
          number of input drops must be >= 2
          mixName from [Mix, Vortex, Tap, Invert, Suspend, Stir]  <- this means nothing to MFSim
    """

    def write_mix(self, instr) -> str:
        _ret = "NODE (%s, MIX, " % str(self.opid)

        self.log.warn("Using default time and mixType values -- these should be IRInstruction attributes discovered"
                      "during parsing")
        time = 10
        mixType = 'Mix'

        # MFSim supports >= 2 input droplets, but BS requires distinct mix operations for every 2 droplets,
        #  hence, we can safely assume every mix has exactly 2 inputs
        _ret += "2, %s, %s)\n" % (str(time), mixType)

        _ret += self.write_edge(self.opid, self.cblock.dag.nodes[instr.defs.name]['iid'])
        return _ret

    """
        An MFSim SPLIT node has 5 parameters:
          nodeid, "SPLIT", number of output drops, time, nodeName
          number of output drops must be >= 2
          nodeName  <- this means nothing to MFSim
    """

    def write_split(self, instr) -> str:
        _ret = "NODE (%s, SPLIT, " % str(self.opid)

        self.log.warn("Using default numDrops and time value for SPLIT; at least numDrops should be a Split "
                      "instruction attribute discovered during parsing")
        numDrops = 2
        time = 2

        _ret += "%s, %s, SPLIT)\n" % (str(numDrops), str(time))

        self.log.warn("Verify split instruction semantics for MFSim target. Not all out edges are correctly built as"
                      "the split does not maintain addressibility to created droplets")

        # TODO: when splits correctly build an array, this must be updated to build edges to proper successors
        # something like:
        #   for succ in self.cblock.dag.nodes[instr.defs.name]['iid']:
        #    _ret += self.write_edge(self.opid, succ)

        _ret += self.write_edge(self.opid, self.cblock.dag.nodes[instr.defs.name]['iid'])
        return _ret

    """
        An MFSim DETECT node has 5 parameters:
          nodeid, "DETECT", number of input drops, time, nodeName
          BS syntax only supports 1 input drop currently
          nodeName  <- this means nothing to MFSim
    """

    def write_detect(self, instr) -> str:
        _ret = "NODE (%s, DETECT, 1, " % str(self.opid)

        self.log.warn("Using default time for DETECT; time should be an IRInstruction attribute discovered "
                      "during parsing")
        time = 10

        _ret += "%s, detect)\n" % str(time)

        # MFSim expects an edge between a use during a detect and the next use
        # if self.cblock.dag.nodes[instr.uses[0].name]:
        #     _ret += self.write_edge(self.opid, self.cblock.dag.nodes[instr.uses[0].name]['iid'])

        to = self.cblock.dag.successors(instr.uses[0].name)
        for key in to:
            to_instr = [x for x in self.cblock.instructions if key in x.uses and x is not instr]
            if to_instr:
                for ti in to_instr:
                    _ret += self.write_edge(self.opid, ti.iid)
            else:
                _ret += self.write_edge(instr.iid, self.tid)
                _ret += self.write_transfer(self.tid, instr.uses[0].points_to, True)
                tn = TransferNode(self.tid, self.cblock.nid, instr.uses[0].points_to, 'out')
                self.tid += 1
                if self.cblock.nid in self.block_transfers:
                    self.block_transfers[self.cblock.nid].add(tn)
                else:
                    self.block_transfers[self.cblock.nid] = {tn}

        # else:
        #    _ret += "transfer out detect"

        return _ret

    """
        An MFSim HEAT node has 4 parameters:
          nodeid, "HEAT", time, nodeName
          nodeName  <- this means nothing to MFSim
    """

    def write_heat(self, instr) -> str:
        _ret = "NODE (%s, HEAT, " % str(self.opid)

        self.log.warn("Using default time for HEAT; time should be an IRInstruction attribute discovered "
                      "during parsing")
        time = 10

        _ret += "%s, heat)\n" % str(time)
        # if node is used in this dag, write edge, else write transfer
        if self.cblock.dag.nodes[instr.defs.name]:
            _ret += self.write_edge(self.opid, self.cblock.dag.nodes[instr.defs.name]['iid'])
        # else:
        #    _ret += "transfer out heat"

        return _ret

    """
        An MFSim DISPOSE (output) node has 4 parameters:
          nodeid, type, sinkName, nodeName
          nodeName  <- this means nothing to MFSim
    """

    def write_dispose(self, instr) -> str:
        _ret = "NODE (%s, OUTPUT, null, drain)\n" % str(self.opid)

        self.log.warn("DISPOSE for mfsim requires to sinkname and type (drain, save, etc).  Using default for now.")
        return _ret

    """
        An MFSim DISPENSE node has 5 parameters:
          nodeid, type, fluidName, volume, nodeName
          nodeName  <- this means nothing to MFSim
    """

    def write_dispense(self, instr) -> str:
        _ret = "NODE (%s, DISPENSE, " % str(self.opid)

        self.log.warn("Using default volume for DISPENSE; this should be an IRInstruction attribute discovered "
                      "during parsing")
        volume = 10

        _ret += "%s, %s, %s)\n" % (instr.uses[0].name, str(volume), instr.defs.points_to)

        to = self.cblock.dag._succ[instr.defs.name]

        for key in to:
            to_instr = [x for x in self.cblock.instructions if x.defs.name is key]
            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)

        return _ret

    def write_td(self, from_dag, to_dag) -> str:
        _ret = ""

        if from_dag in self.block_transfers:
            for to in self.block_transfers[from_dag]:
                if to.type is 'out':
                    if to_dag in self.block_transfers:
                        for ti in self.block_transfers[to_dag]:
                            if ti.type is 'in' and ti.name is to.name:
                                _ret += "TD(DAG%s, %s, DAG%s, %s)\n" % (from_dag, to.tid, to_dag, ti.tid)

        _ret += "\n"
        return _ret

    def write_exp(self, cond: Conditional, exp_id: int, from_dag, to_dag, cond_type='UNCOND') -> str:
        _ret = ""
        if isinstance(cond.right, Conditional):
            # nested conditional
            _ret += "subexpressions\n"
        else:
            _ret += "EXP(%s, " % str(exp_id)

        if cond_type is 'UNCOND':
            _ret += "TRUE, UNCOND, DAG%s)\n" % str(from_dag)
        elif cond_type is 'LOOP':
            if cond.cond_type is 'repeat':
                _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(to_dag), int(cond.left.value))
            else:  # must be a while?
                _ret += "while\n"
        elif cond_type is 'IF':
            if cond.cond_type is 'if':
                # ONE_SENSOR, relop, depDag, depNodeID, value)
                relop = "Unrecognized relationtional operator"
                if cond.relop is RelationalOps.LTE:
                    relop = "LoE"
                elif cond.relop is RelationalOps.GTE:
                    relop = "GoE"
                elif cond.relop is RelationalOps.GT:
                    relop = "GT"
                elif cond.relop is RelationalOps.LT:
                    relop = "LT"
                elif cond.relop is RelationalOps.EQUALITY:
                    relop = "EQ"
                cond_var = None
                for v in cond.uses:
                    if isinstance(v, RenamedVar):
                        cond_var = v
                        break
                if cond_var is None:
                    self.log.fatal("Could not find a conditional variable")
                    exit(-1)

                depDag = None
                # current block has the definition to this conditional variable
                if cond_var.name in self.cblock.defs:
                    depDag = from_dag
                else:
                    self.log.warn("need to find block where condition variable is")
                    exit(-1)

                dep_node_id = -1
                for instr in self.cblock.instructions:
                    if instr.defs is not None:
                        if instr.defs.points_to is cond_var.points_to:
                            dep_node_id = instr.iid
                            break

                _ret += "ONE_SENSOR, %s, DAG%s, %s, %s)\n" % (relop, str(depDag), str(dep_node_id), int(cond.right.value))
            elif cond.cond_type is 'else':
                _ret += "else\n"

        # transfer droplets if necessary
        _ret += self.write_td(from_dag, to_dag)

        self.expid += 1

        return _ret

    def write_cond(self, cond: Conditional, group_num: int, dep_dags, num_branch_dags: int, branch_dags, exp_id: int,
                   num_dep_dags=1, cond_type='UNCOND') -> str:
        # TODO: implement compound expression translation to MFSim
        # we only implement single dependency with a single expression for now
        _ret = "COND(%s, %s, " % (str(group_num), str(num_dep_dags))
        for dag in dep_dags:
            _ret += "DAG%s, " % dag

        _ret += "%s, " % str(num_branch_dags)

        for dag in branch_dags:
            _ret += "DAG%s, " % dag

        _ret += "%s)\n" % str(exp_id)

        # build expression(s)
        if cond_type is 'UNCOND':
            _ret += self.write_exp(cond, exp_id, dep_dags[0], branch_dags[0])
        elif cond_type is 'LOOP':
            _ret += self.write_exp(cond, exp_id, dep_dags[0], branch_dags[0], 'LOOP')
        elif cond_type is 'IF':
            _ret += self.write_exp(cond, exp_id, dep_dags[0], branch_dags[0], 'IF')

        # buid transfer droplet(s), if any

        return _ret

    def transform(self):
        self.build_cfg()
        # self.log.debug("MFSimTarget not yet implemented!")
        for root in self.program.functions:
            self.root = root
            exp_name = self.config.input.rsplit('/', 1)[1][:-3]  # get file input name -'.bs'
            cfg_file = open("%s.cfg" % exp_name, "w")
            cfg_file.write("NAME(%s.cfg)\n\n" % exp_name)

            # conditional groups
            cgs = dict()

            for bid, block in self.program.functions[root]['blocks'].items():
                self.cblock = block

                write = False
                for instr in block.instructions:
                    if instr.name in ['MIX', 'DISPENSE', 'DISPOSE', 'HEAT', 'SPLIT', 'DETECT']:
                        write = True
                        break

                if not write:
                    continue
                # # we write the conditions to a list to be appended to the .cfg file
                # if block.dag is None:
                #     cgs[bid] = set()
                #     """
                #         for each conditional group, we have a variable number of COND, EXP, and TD nodes
                #         COND: variable number of parameters as:
                #               group number, # dep. dags, comma-sep-list of dep. dags, # branch dags, comma-sep-list
                #                  of branch dags, expression ID
                #         EXP: parameters as:
                #               expression ID (matches COND)
                #               variable based on expression-type
                #         TD: transfer droplet for each routed droplet, parameters are:
                #               DAGfrom, nodeIdFrom, DAGto, nodeIDTo
                #
                #         each transfer droplet will have a corresponding TRANSFER_OUT/_IN in the appropriate dags,
                #     """
                #     # TODO: conditionals translation

                cfg_file.write("DAG(DAG%s)\n" % str(bid))

                queue = deque()
                globalz = dict()
                dag_file = open("%s_DAG%s.dag" % (exp_name, str(bid)), "w")
                dag_file.write("DagName (DAG%s)\n" % str(bid))

                # for all uses without defs, we must transfer in droplets
                already_transferred_in = dict()
                for node in block.instructions:

                    if node.name in ['BINARYOP', 'CONDITIONAL', 'DISPENSE']:
                        continue

                    # as SSA renaming is not correct, we must work around the names to find proper transfer nodes
                    # TODO: update transfer_in discovery when SSA renaming is fixed -- will simplify this a lot
                    # for each use, we must check if predecessors in this block defined it (original name, SSA is broken)
                    #  if no def from predecessor, then
                    for use in node.uses:
                        tn = None
                        if use.points_to in already_transferred_in:
                            continue
                        if use.name not in block.defs:
                            already_transferred_in[use.points_to] = True
                            dag_file.write(self.write_transfer(self.tid, use.points_to, False))
                            dag_file.write(self.write_edge(self.tid, node.iid))
                            tn = TransferNode(self.tid, bid, use.points_to, 'in')
                            block.defs.add(use.points_to)
                            self.tid += 1
                        if tn is not None:
                            if bid in self.block_transfers:
                                self.block_transfers[bid].add(tn)
                            else:
                                self.block_transfers[bid] = {tn}

                for node in block.instructions:
                    self.opid = node.iid

                    if node.op is IRInstruction.DETECT:
                        dag_file.write(self.write_detect(node))
                    elif node.op is IRInstruction.MIX:
                        dag_file.write(self.write_mix(node))
                    elif node.op is IRInstruction.SPLIT:
                        dag_file.write(self.write_split(node))
                    elif node.op is IRInstruction.HEAT:
                        dag_file.write(self.write_heat(node))
                    elif node.op is IRInstruction.DISPOSE:
                        dag_file.write(self.write_dispose(node))
                    elif node.op is IRInstruction.DISPENSE:
                        dag_file.write(self.write_dispense(node))
                    elif node.op is IRInstruction.PHI or node.op is IRInstruction.CONDITIONAL:
                        continue
                    else:
                        self.log.warn("Unrecognized/unsupported instruction type: %s" % node.name)

                # this is a bit of a hack, because SSA renaming is not working properly atm.
                # TODO: update transfer_out discovery when SSA renaming is fixed -- will simplify this a lot
                # for all defs without uses, we must transfer out (if used elsewhere)
                #   or dispose (if never used again)
                # For now, for each __def in the block, we get the original variable name (_def) and instruction (i)
                #  Then, we check if __def is used in the block (we do not need to transfer)
                #    if not, we check each successor block (succ): for each instruction si in succ, we check
                #    if their uses points to _def, if so, we must transfer.
                for rdef in block.defs:
                    _def = None
                    skip = False
                    for i in block.instructions:
                        if i.name in ['PHI', 'BINARYOP', 'CONDITIONAL', 'DISPOSE', 'DETECT']:
                            skip = True
                            continue
                        if i.defs.name is rdef:
                            skip = False
                            _def = i.defs.points_to
                            instr = i
                            break
                        # elif i.name is 'DETECT' and rdef in already_transferred_in:
                        #      skip = False
                        #      _def = rdef
                        #      instr = i
                        #      break

                    if skip:
                        continue

                    transferred = False
                    tn = None
                    if rdef not in block.uses:
                        # check if used in any successor blocks
                        if block.dag is not None:
                            # list of reachable block ids
                            reachable = (
                               {x for v in dict(nx.bfs_successors(self.cfg['graph'], bid)).values() for x in v})
                            for s in reachable:
                                if transferred:
                                    break
                                # get successor block
                                sblock = self.program.functions[root]['blocks'][s]
                                for si in sblock.instructions:
                                    if transferred:
                                        break
                                    for use in si.uses:
                                        if isinstance(use, RenamedVar) and _def is use.points_to:
                                            dag_file.write(self.write_edge(instr.iid, self.tid))
                                            dag_file.write(self.write_transfer(self.tid, _def, True))
                                            tn = TransferNode(self.tid, bid, _def, 'out')
                                            self.tid += 1
                                            transferred = True
                                            break

                    else:
                        transferred = True
                    if not transferred:  # need to dispose
                        print("need to dispose %s" % rdef)
                    if tn is not None:
                        if bid in self.block_transfers:
                            self.block_transfers[bid].add(tn)
                        else:
                            self.block_transfers[bid] = {tn}

                dag_file.close()

            # now build the conditions, with their expressions and potential transfer droplets
            # COND/EXP cases:
            #   1) edge on CFG from n to n' with no conditional = UNCOND transfer.
            #   2) edges on CFG from n to {t, f} with a conditional in a block with no executable instructions
            #      this is a loop.  if repeat, we have "LOOP_NUM" condition.  if not a repeat, need to link
            #      "ONE_SENSOR" to the appropriate detect instruction
            #      This is the most difficult case, as MFSim treats all loops as do-while loops.  we'll need
            #        to make transfer from pred(n) to t, edge from t to t and t to f.
            #   3)  edge on CFG from n to n' with a conditional in a block with executable instructions
            #      this is an if/else block.  translation is straightforward
            # TD -- each transferred droplet should be accounted for in self.block_transfers.  need to map COND/EXP to
            #    the appropriate transferred droplet

            # store elements as: bid: (true branch, false branch)

            # for each edge in bb_graph, must have corresponding in .cfg

            edges_not_translated = list(nx.edges(self.cfg['graph']))

            conditional_groups = dict()

            for bid, block in self.program.functions[root]['blocks'].items():
                if block.instructions is None:
                    continue
                cond = False
                executable = False
                if block.dag is not None:
                    for instr in block.instructions:
                        if cond and executable:
                            break
                        if instr.name is 'CONDITIONAL':
                            cond = True
                        if instr.name in ['MIX', 'DETECT', 'SPLIT', 'HEAT', 'DISPENSE', 'DISPOSE']:
                            executable = True

                    # deal with successor loop headers, which will take care of [current : translated]:
                    #   bid->succ               :   bid->true
                    #   succ->true              :   [no translation]
                    #   succ->false             :   true->false
                    #   back-edge(s) to succ    :   back1->true...backn->true
 #                   for succ_id in self.program.functions[root]['graph'].succ[bid]:
                    for succ_id in self.cfg['graph'].successors(bid):
                        # we know there is an edge from bid to succ_id, need to check if bid or succ_id is a loop header
                        if (bid, succ_id) not in edges_not_translated:
                            continue
                        if bid in self.loop_headers:
                            # bid is loop header
                            print("if I take care of everything already, then continue?")
                            continue
                        elif succ_id in self.loop_headers:
                            # unconditional branch into loop (MFSim interprets all loops as do-while)
                            conditional_groups[self.cgid] = []
                            conditional_groups[self.cgid].append(self.write_cond(self.loop_headers[succ_id]['instr'],
                                                                                 self.cgid, [bid], 1,
                                                                                 [self.loop_headers[succ_id]['t']],
                                                                                 self.expid, 1))
                            edges_not_translated.remove((bid, succ_id))
                            edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['t']))
                            self.cgid += 1

                            conditional_groups[self.cgid] = []
                            # find all back edges -- this is probably wrong, as these may fall into different CGs
                            back_edges = [x for x in edges_not_translated if x[1] is succ_id]
                            for be in back_edges:
                                conditional_groups[self.cgid].append(
                                    self.write_cond(self.loop_headers[succ_id]['instr'], self.cgid,
                                                    [be[0]], 1,
                                                    [self.loop_headers[succ_id]['t']],
                                                    self.expid, 1, 'LOOP'))
                                edges_not_translated.remove((be[0], succ_id))

                            # deal with exit from loop
                            conditional_groups[self.cgid].append(self.write_cond(self.loop_headers[succ_id]['instr'],
                                                                                 self.cgid,
                                                                                 [self.loop_headers[succ_id]['t']], 1,
                                                                                 [self.loop_headers[succ_id]['f']],
                                                                                 self.expid, 1, ))
                            edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['f']))
                            self.cgid += 1
                        else: #dealing with if conditional
                            if cond and executable:
                                self.cblock = block
                                conditional_groups[self.cgid] = []
                                for instr in self.program.functions[root]['blocks'][bid].instructions:
                                    if instr.op is IRInstruction.CONDITIONAL:
                                        conditional_groups[self.cgid].append(
                                            self.write_cond(self.cfg[bid][instr.iid]['instr'],
                                                            self.cgid, [bid], 1,
                                                            [self.cfg[bid][instr.iid]['t']],
                                                            self.expid, 1, 'IF'))
                                        edges_not_translated.remove((bid, self.cfg[bid][instr.iid]['t']))
                                        if self.cfg[bid][instr.iid]['f'] is not None:
                                            conditional_groups[self.cgid].append(
                                                self.write_cond(self.cfg[bid][instr.iid]['instr'],
                                                                self.cgid, [bid], 1,
                                                                [self.cfg[bid][instr.iid]['f']],
                                                                self.expid, 1))
                                            edges_not_translated.remove((bid, self.cfg[bid][instr.iid]['f']))
                                print("what to do")
                                self.cgid += 1

            cfg_file.write("\nNUMCGS(%s)\n\n" % conditional_groups.__len__())

            for cg in conditional_groups.values():
                for val in cg:
                    cfg_file.write(val)

            cfg_file.close()

        return True

    def write_branch(self) -> str:
        pass

    def write_expression(self) -> str:
        pass
