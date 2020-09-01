import networkx as nx

from compiler.data_structures import IRInstruction
from compiler.data_structures import RelationalOps
from compiler.data_structures.ir import Conditional
from compiler.data_structures.variable import *
from compiler.targets.base_target import BaseTarget
from compiler.data_structures.ir import TempConstraint
from compiler.data_structures.ir import TimeConstraint


class TransferNode:

    def __init__(self, tid, bid, name, ttype):
        self.tid = tid
        self.iid = tid
        self.name = name
        self.bid = bid
        self.type = ttype

    def __str__(self):
        return "{}: {}->{}".format(self.name, self.bid, self.tid)


class MFSimTarget(BaseTarget):

    def __init__(self, program):
        super().__init__(program, "MFSimTarget")
        self.cblock = None
        self.opid = None
        self.root = None
        self.edges_not_translated = None
        self.predecessor_edges = list()
        self.cgid = 0
        self.expid = 0
        self.cfg = dict()
        self.block_transfers = dict()
        self.loop_headers = dict()
        self.cgid_pair = dict() #to ensure cgid stay consistent
        self.live_droplets = list() #to ensure droplets are passed along accoringly
        self.split_offset = list() #for split recursion
        self.curr_split_offset = list() #for split recursion
        # start transfer nodes from id 100.
        if self.config.debug:
            self.log.debug("Statically starting transfer IDs from 100. This could be an issue for very large assays.")
        if not self.config.output:
            self.log.fatal("MFSim target requires an output path to be specified.  Include \"-o <path/to/output/>\" in arguments list.")
            exit(-1)
        self.tid = 100
        self.num_dags = 0
        self.num_cgs = 0
        self.num_edges = 0
        self.num_mixes = 0
        self.num_splits = 0
        self.num_detects = 0
        self.num_heats = 0
        self.num_transfers = 0
        self.num_dispense = 0
        self.num_dispose = 0

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
                    if instruction.op is IRInstruction.NOP:
                        continue

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

                        if bid in self.loop_headers:
                            self.loop_headers[bid].add({'instr': instruction, 't': true_block, 'f': false_block})
                        else:
                            if not true_label.startswith('bsbbif'):
                                self.loop_headers[bid] = {'instr': instruction, 't': true_block, 'f': false_block}

                        curr[instruction.iid] = dict()
                        curr[instruction.iid] = {'instr': instruction, 'f': false_block,
                                                 't': true_block}
                        if instruction.left['var'].name.startswith("REPEAT"):
                            curr[instruction.iid]['c'] = 'repeat'
                            curr[instruction.iid]['repeat'] = instruction.left['var'].value
                        else:  # could be nested conditional
                            curr[instruction.iid]['c'] = instruction.relop
                            #if self.config.debug:
                                #self.log.warning("TEST non-repeat/nested CONDITIONALS")
                    #  non-conditionals
                    elif hasattr(instruction, 'uses'):
                        # Case x = op y (dispense, heat, dispose, store)
                        if len(instruction.uses) == 1:
                            # Look at the r-value.
                            # if instruction.name == "DISPOSE":  # if we dispose this droplet, then we do not need to transfer
                            #     if self.config.debug:
                            #         self.log.warning("Removing outgoing cfg edges from block {}; verify .cfg file has "
                            #                       "correct edges when multiple droplets exist in a dag including a "
                            #                       "dispose.".format(bid))
                            #     remove_edges_from.add(bid) (Old)
                            use = next(iter(instruction.uses))
                            if use['name'] not in leafs:
                                dag.add_node(use['name'], type="variable")
                                leafs.add(use['name'])
                                leaf = use['name']
                            else:
                                leaf = use['name']
                            # Do the same thing, except for the l-value.
                            if instruction.defs:
                                if instruction.defs['name'] not in tags:
                                    dag.add_node(leaf, iid=instruction.iid, op=instruction.op.name, type="register")
                                    var_def = instruction.defs['name']
                                    tags[instruction.defs['name']] = var_def
                                else:
                                    var_def = instruction.defs['name']
                                dag.add_edge(leaf, var_def)
                        else:
                            # Case x = y op z (mix, split, arithmetic)
                            var_def = instruction.defs['name']
                            dag.add_node(var_def, iid=instruction.iid, op=instruction.op.name, type="register")
                            tags[var_def] = var_def
                            for use in instruction.uses:
                                if instruction.op is IRInstruction.PHI:
                                    leaf = use
                                else:
                                    leaf = use['name']
                                if leaf not in leafs:
                                    dag.add_node(leaf, type="variable")
                                    leafs.add(leaf)
                                dag.add_edge(leaf, var_def)

                    else:  # what instruction is being missed
                        if self.config.debug:
                            self.log.info(instruction)

                    # if a material is disposed, it should not define a new material for later use
                    # if instruction.op is IRInstruction.DISPOSE:
                    #     defined = instruction.defs['var'].name
                    #     #instruction.defs.name = 'gone!'
                    #     block.defs.remove(defined)
                    #     #predecessors = list(dag.predecessors(defined))
                    #     #for pred in predecessors:
                    #     #    dag.remove_edge(pred, defined)
                    #     #in the case where the only def in a block has been removed because it was a dipose,
                    #     #   we do not need any outgoing edges.
                    #     # old TO DO: test case: transfer_in A, B; dispose A (do nothing with B).
                    #     #   if this fails, we could explicitly add a def to the block for transfer_ins prior to
                    #     #   running these checks (in transform())
                    #     if len(block.defs) is 0:
                    #         remove_edges_from.add(bid)

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

    def get_dependent_instr(self, instr, uses):
        """
           when a droplet has multiple successors in the DAG, and is not a split, then there is a use that does not consume
           the droplet.  In this case, we must find the successor that uses the droplet without consuming.  this is the
           instruction that should receive the edge
        :param instr:
        :param uses:
        :return:
        """
        _ret = list()
        #used to be: check = instr.defs['var'].name
        check = instr.uses[0]['name']
        found_instr = False
        for i in self.cblock.instructions:
            if i is instr:
                found_instr = True
                continue
            if not found_instr:
                continue
            if i.op in {IRInstruction.NOP, IRInstruction.CONDITIONAL}:  #used to be NOP only
                continue
            self.log.info(i)
            if instr.op is IRInstruction.DETECT: #Detect is looking for uses rather than defs
                for use in i.uses:
                    if use['name'] in uses:
                        if i.iid != check:
                            if not _ret:
                                _ret.append(use['name'])
            else:
                if i.defs['name'] in uses:  # this instruction is one of the uses
                    if i.iid != check:  #used to be either if i.defs['var'].name != check:  #if i.uses[0]['name'] != check:
                        if not _ret:
                            _ret.append(i.defs['var'].name) #used to be _ret.append(i.defs['var'].points_to.name)

        if len(_ret) < 1:
            self.log.fatal("A non-split instruction has multiple successors!")
            exit(-1)

        return _ret

    def write_transfer(self, id, name, out=False) -> str:
        self.num_transfers += 1
        return "NODE (%s, %s, %s)\n" % (str(id), "TRANSFER_OUT" if out else "TRANSFER_IN", name)

    def write_edge(self, _from, _to) -> str:
        # should not be trying to write an edge
        if self.cblock.dag is None:
            if self.config.debug:
                self.log.warning("write edge returning without writing an edge")
            pass
        self.num_edges += 1
        return "EDGE (%s, %s)\n" % (_from, _to)

    def write_mix(self, instr) -> str:
        """
              An MFSim MIX node has 5 parameters:
              nodeid, "MIX", number of input drops, time, mixName
              number of input drops must be >= 2
              mixName from [Mix, Vortex, Tap, Invert, Suspend, Stir]  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = "NODE (%s, MIX, " % str(self.opid)

        #if self.config.debug:
        #    self.log.warning("Using default time and mixType values -- these should be IRInstruction attributes discovered"
        #                  "during parsing") (Old)
        time = 10

        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
                break
        # mixType = '_'.join([x['var'].name for x in instr.uses])

        # MFSim supports >= 2 input droplets, but BS requires distinct mix operations for every 2 droplets,
        #  hence, we can safely assume every mix has exactly 2 inputs
        _ret += "2, %s, %s)\n" % (str(time), instr.defs['var'].points_to.name)

        to = list(self.cblock.dag.successors(instr.defs['var'].name))

        if len(to) > 1:
            found_instr = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if x.defs['var'].name == instr.defs['var'].name:
                    to = list() #used to be to = list(instr.defs['var'].name)
                    to.append(instr.defs['var'].points_to.name) #used to be just .name
                    break
                break

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)
            to = list(dict.fromkeys(to))  # remove potential duplicates and keep order

        for key in to:
            to_instr = [x for x in self.cblock.instructions if x.defs and x.defs['var'].name is key]
            for ti in to_instr:
                if ti.iid == self.opid:
                    continue
                _ret += self.write_edge(self.opid, ti.iid)
                break

        for key in to:
            to_instr = [x for x in self.cblock.instructions if x.defs and x.defs['var'].points_to.name is key]
            for ti in to_instr:
                if ti.iid == self.opid:
                    continue
                _ret += self.write_edge(self.opid, ti.iid)
                break

        self.num_mixes += 1
        return _ret

    def write_split_helper(self, instr):
        """
                      Helper function for split recursion
                :param instr:
                :return: chain of all splits as a str:
                """
        if instr.split_size == 2:
            _ret = self.write_split(instr)
            return _ret

        else:
            _ret = "NODE (%s, SPLIT, " % str(self.opid)

            numDrops = 2
            time = 2

            for t in instr.meta:
                if type(t) is TimeConstraint:
                    time = t.quantity
                    break

            n = instr.split_size
            offset = n/2

            _ret += "%s, %s, SPLIT)\n" % (str(numDrops), str(time))
            _ret += self.write_edge(self.opid, self.opid + 1)
            _ret += self.write_edge(self.opid, self.opid + int(offset))
            self.num_splits += 1

            valid = True
            while n != 1 and n > 1:
                if n % 2 != 0:
                    valid = False
                n = n / 2

            if not valid:
                self.log.fatal("A split instruction has an invalid number of successors!")
                exit(-1)
            else: #number is valid 2, 4, 8, ect, continue
                #handle left and right sides
                left_instr = deepcopy(instr)
                left_instr.split_size = instr.split_size/2
                left_instr.id_counter += 1
                left_instr.iid += 1
                left_instr.defs['size'] = left_instr.defs['size']/2
                self.opid += 1
                #_ret += self.write_edge(self.opid, self.opid + 1)
                hold_left_and_right = self.write_split_helper(left_instr)
                right_instr = deepcopy(left_instr)
                right_instr.id_counter += 1
                right_instr.iid += 1
                self.opid += 1
                hold_left_and_right += self.write_split_helper(right_instr)
                _ret += hold_left_and_right
                return _ret

    def write_split(self, instr) -> str:
        """
                An MFSim SPLIT node has 5 parameters:
                  nodeid, "SPLIT", number of output drops, time, nodeName
                  number of output drops must be >= 2 and an exponent of 2
                  nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = "NODE (%s, SPLIT, " % str(self.opid)

        #if self.config.debug:
        #    self.log.warning("Using default numDrops and time value for SPLIT; at least numDrops should be a f "
        #                  "instruction attribute discovered during parsing") (Old) Default time value is expected
        numDrops = 2
        time = 2

        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
                break

        _ret += "%s, %s, SPLIT)\n" % (str(numDrops), str(time))

        #if self.config.debug:
            #self.log.warning(
                #"Verify split instruction semantics for MFSim target. Not all out edges are correctly built as"
                #"the split does not maintain addressibility to created droplets")
                #(Old)

        # Old TO DO: when splits correctly build an array, this must be updated to build edges to proper successors
        # something like:
        #   for succ in self.cblock.dag.nodes[instr.defs['name']]['iid']:
        #    _ret += self.write_edge(self.opid, succ)

        to = list(self.cblock.dag.successors(instr.defs['var'].name))
        to = [x for x in to if x == instr.defs['name']]

        for key in to:
            to_instr = []
            # as long as order of instructions is maintained this works.
            #found_instr = False
            counter = 0
            while counter != 2:
                found_instr = False
                for x in self.cblock.instructions:
                    if x.name is 'NOP':
                        continue
                    if x.uses[0]['name'] is instr.uses[0]['name'] and x.name is 'SPLIT':
                        found_instr = True
                        continue
                    if not found_instr:
                        continue
                    if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH}:
                        for y in x.uses:
                            if y['var'].name == key:
                                if y['offset'] in self.split_offset or counter is 2:
                                    continue
                                if len(self.curr_split_offset) is 0:
                                    if y['offset'] is 0:
                                        self.curr_split_offset.append(y['offset'])
                                        self.split_offset.append(y['offset'])
                                        to_instr.append(x)
                                        counter += 1
                                        break
                                    else:
                                        continue
                                if y['offset'] is self.curr_split_offset[0] + 1:
                                    self.curr_split_offset = list()
                                    self.curr_split_offset.append(y['offset'])
                                else:
                                    continue
                                self.split_offset.append(y['offset'])
                                to_instr.append(x)
                                counter += 1
                                break

            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)

        self.num_splits += 1
        return _ret

    def write_detect(self, instr) -> str:
        """
            An MFSim DETECT node has 5 parameters:
              nodeid, "DETECT", number of input drops, time, nodeName
              BS syntax only supports 1 input drop currently
              nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = "NODE (%s, DETECT, 1, " % str(self.opid)

        #if self.config.debug:
        #    self.log.warning("Using default time for DETECT; time should be an IRInstruction attribute discovered "
        #                  "during parsing") (Old)
        time = 10

        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
                break

        _ret += "%s, %s(%s))\n" % (str(time), instr.defs['var'].points_to.name, instr.uses[1]['var'].points_to.name)

        #for ti in to_instr:
         #   _ret += self.write_edge(self.opid, ti.iid) #Old method

        to = list(self.cblock.dag.successors(instr.uses[1]['name'])) #Better method
        to = [x for x in to if x != instr.defs['name']]

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)
            to = list(dict.fromkeys(to))  # remove potential duplicates and keep order

        for key in to:
            to_instr = []
            # as long as order of instructions is maintained this works.
            found_instr = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH}:
                    for y in x.uses:
                        if y['var'].name == key:
                            to_instr.append(x)
                            break

            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)
                break

        self.num_detects += 1
        return _ret

    def write_heat(self, instr) -> str:
        """
             An MFSim HEAT node has 4 parameters:
                  nodeid, "HEAT", time, nodeName
                  nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = "NODE (%s, HEAT, " % str(self.opid)

        #if self.config.debug:
        #    self.log.warning("Using default time for HEAT; time should be an IRInstruction attribute discovered "
        #                  "during parsing") (Old)
        time = 10

        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
                break

        _ret += "{}, {})\n".format(str(time), instr.uses[0]['var'].points_to.name)

        to = list(self.cblock.dag.successors(instr.defs['var'].name))

        if len(to) > 1:
            found_instr = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if x.defs['var'].name == instr.defs['var'].name:
                    to = list() #old initialization to = list(instr.defs['var'].name)
                    to.append(instr.defs['var'].name) #used to be just .name
                    break
                break

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)
            to = list(dict.fromkeys(to))  # remove potential duplicates and keep order

        for key in to:
            to_instr = []
            # as long as order of instructions is maintained this works.
            # ideally, the SSA form would have explicit defs for all heats, SSA is fixed now
            found_instr = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH, IRInstruction.CONDITIONAL}:
                    if x.defs['var'].name  == key:
                        to_instr.append(x)
                        break

            for ti in to_instr:
                if ti.iid == self.opid:
                    continue
                _ret += self.write_edge(self.opid, ti.iid)
                break

            self.num_heats += 1
        return _ret

    def write_dispose(self, instr) -> str:
        """
               An MFSim DISPOSE (output) node has 4 parameters:
              nodeid, type, sinkName, nodeName
              nodeName  <- this means nothing to MFSim
        :return:
        """
        _ret = "NODE (%s, OUTPUT, null, %s)\n" % (str(self.opid), instr.uses[0]['var'].points_to.name)

        live_drops = list(self.live_droplets) #done to fix an issue when a droplet is "killed"
        for a, b in live_drops:
            if b == instr.uses[0]['var'].points_to.name:
                self.live_droplets.remove((a, b))

        #if self.config.debug:
        #    self.log.warning(
        #        "DISPOSE for mfsim requires the sinkname and type (drain, save, etc).  Using default for now. Only needed for archfile, defaults are fine currently")
        self.num_dispose += 1
        return _ret

    def write_dispense(self, instr) -> str:
        """
             An MFSim DISPENSE node has 5 parameters:
              nodeid, type, fluidName, volume, nodeName
              nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = "NODE (%s, DISPENSE, " % str(self.opid)

        #if self.config.debug:
        #    self.log.warning("Using default volume for DISPENSE; this should be an IRInstruction attribute discovered "
        #                  "during parsing") (Old)
        #volume = 10


        capture = instr.defs['var'].volumes
        volume = next(iter(capture.values()))

        _ret += "%s, %s, %s)\n" % (instr.uses[0]['name'], str(volume), instr.defs['var'].points_to.name)

        to = list(self.cblock.dag._succ[instr.defs['var'].name])

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)

        for key in to:
            to_instr = [x for x in self.cblock.instructions if x.defs is not None and x.defs['var'].name is key]
            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)

        #for key in to: (not necessary)
        #    to_instr = [x for x in self.cblock.instructions if x.defs is not None and x.defs['var'].points_to.name is key]
        #    for ti in to_instr:
        #        _ret += self.write_edge(self.opid, ti.iid)

        self.num_dispense += 1
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


        if cond_type is 'UNCOND':
            _ret += "EXP(%s, " % str(exp_id)
        elif isinstance(cond.right, Conditional):
            # nested conditional
            _ret += "subexpressions\n"
        else:
            _ret += "EXP(%s, " % str(exp_id)

        if cond_type is 'UNCOND':
            _ret += "TRUE, UNCOND, DAG%s)\n" % str(from_dag)
        elif cond_type is 'LOOP':
            if cond.left['name'].startswith('REPEAT'):  # .cond_type is 'repeat':
                _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(from_dag), int(cond.left['var'].value.value[0])) #changed str(to_dag) to str(from_dag)
            else:  # must be a while?
                _ret += "while)\n" #this is the simple while setup currently, can be changed to include more information
        elif cond_type is 'IF':
            # ONE_SENSOR, relop, depDag, depNodeID, value)
            relop = "Unrecognized relational operator"
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
                if isinstance(v['var'], RenamedSymbol):
                    cond_var = v
                    break
            if cond_var is None:
                self.log.fatal("Could not find a conditional variable")
                exit(-1)

            depDag = None
            dep_node_id = -1
            # current block has the definition to this conditional variable
            if cond_var['var'].name in self.cblock.defs:
                depDag = from_dag
            else:
                #predes = reversed(list(self.program.functions['main']['graph'].predecessors(exp_id))) (Old method)
                predes = reversed(list(self.program.functions['main']['blocks'])) #find the last def of this variable
                for p in predes:
                    block = self.program.functions['main']['blocks'][p]
                    if cond_var['var'].name in block.defs:
                        depDag = p
                        for instr in block.instructions:
                            if instr.defs is not None:
                                if instr.defs['var'].points_to is cond_var['var'].points_to:
                                    dep_node_id = instr.iid
                                    break
                #if self.config.debug:
                    #self.log.warning("need to find block where condition variable is")
                #raise NotImplementedError("the current block does not have the definition to this conditional variable") (Old)

            for instr in self.cblock.instructions: #find the source instr
                if instr.defs is not None:
                    if instr.defs['var'].points_to is cond_var['var'].points_to:
                        dep_node_id = instr.iid
                        break

            _ret += "ONE_SENSOR, %s, DAG%s, %s, %s)\n" % (
            relop, str(depDag), str(dep_node_id), int(cond.right['var'].value.value[0]))

        # transfer droplets if necessary
        _ret += self.write_td(from_dag, to_dag)

        self.expid += 1

        return _ret

    def write_cond(self, cond: Conditional, group_num: int, dep_dags, num_branch_dags: int, branch_dags, exp_id: int,
                   num_dep_dags=1, cond_type='UNCOND') -> str:
        # TO DO: implement compound expression translation to MFSim
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

        return _ret

    def create_conditional_groups(self, edges_not_translated):
        conditional_groups = dict()

        edges_not_translated_save = deepcopy(edges_not_translated)

        seen_pair = list()

        no_trans = False
        if len(self.block_transfers) == 0:
            no_trans = True

        if not no_trans:
            no_trans = True
            for a in self.block_transfers:
                b = self.block_transfers[a]
                for c in b:
                    if c.type is 'out':
                        no_trans = False

        while len(edges_not_translated) > 0:
            for bid, block in self.program.functions['main']['blocks'].items():
                if block.instructions is None:
                    for e in edges_not_translated:
                        if e[0] == bid:
                            edges_not_translated.remove(e)
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
                        # we know there is an edge from bid to succ_id, need to check if bid or succ_id is a loop
                        # header
                        if (bid, succ_id) not in edges_not_translated:
                            continue
                        if bid in self.loop_headers:
                            # bid is loop header
                            edges_not_translated.remove((bid, succ_id))
                            #print("if I take care of everything already, then continue?") - Simply remove in this case
                            continue
                        elif succ_id in self.loop_headers:
                            #if len(edges_not_translated) == 1:  # catch a stragling condition that doesnt belong (Old way of catching extra expression)
                                #edges_not_translated.remove((bid, succ_id))
                                #continue
                            # unconditional branch into loop (MFSim interprets all loops as do-while)
                            # ensure cgid groups stay together
                            cgid = self.cgid
                            if not no_trans and bid not in self.block_transfers:
                                edges_not_translated.remove((bid, succ_id))
                                continue
                            if bid not in self.cgid_pair.keys():
                                self.cgid_pair[bid] = self.cgid
                            else:
                                check = self.cgid_pair[bid]
                                if check != self.cgid:
                                    cgid = check
                            if self.loop_headers[succ_id]['t'] in self.block_transfers or no_trans:
                                #if (succ_id, self.loop_headers[succ_id]['t']) not in edges_not_translated: (Old way of removing the edge if second edge doesn't exist, no longer an issue)
                                    #edges_not_translated.remove((bid, succ_id))
                                    #self.cgid += 1
                                    #break
                                if not no_trans:
                                    out = False
                                    for node in self.block_transfers[bid]:
                                        if node.type is 'out':
                                            out = True
                                    if not out: #this edge should not be here, remove
                                        edges_not_translated.remove((bid, succ_id))
                                        self.cgid_pair.pop(bid)
                                        self.cgid += 1
                                        continue
                                    if (bid, self.loop_headers[succ_id]['t']) in seen_pair: #if already handled, move on
                                        edges_not_translated.remove((bid, succ_id))
                                        self.cgid += 1
                                        continue
                                conditional_groups[self.cgid] = []
                                conditional_groups[self.cgid].append(
                                self.write_cond(self.loop_headers[succ_id]['instr'],
                                                cgid, [bid], 1,
                                                [self.loop_headers[succ_id]['t']],
                                                self.expid, 1))
                                seen_pair.append((bid, self.loop_headers[succ_id]['t']))
                                if 'w' in str(self.program.functions['main']['blocks'][succ_id].label) and self.loop_headers[succ_id]['f'] is not None: #if conditional is a while, need a path to the false branch as well
                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'],
                                                        cgid, [bid], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1))
                                    seen_pair.append((bid, self.loop_headers[succ_id]['f']))
                                edges_not_translated.remove((bid, succ_id))
                                if edges_not_translated:
                                    if (succ_id, self.loop_headers[succ_id]['t']) in edges_not_translated: #remove this edge if there
                                        edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['t']))
                                    self.cgid += 1
                                else:
                                    continue
                            elif self.loop_headers[succ_id]['t'] is None and bid == next(iter(self.block_transfers)): #this is here for instances of nested conditionals with non active dags such that 't' path is None
                                early_initialize = False
                                if 'w' in str(self.program.functions['main']['blocks'][succ_id].label) and self.loop_headers[succ_id]['f'] is not None: #if conditonal is also a while, must include path to the false branch
                                    conditional_groups[self.cgid] = []
                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'],
                                                        cgid, [bid], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1))
                                    seen_pair.append((bid, self.loop_headers[succ_id]['f']))
                                    early_initialize = True
                                val2 = succ_id
                                if len(self.block_transfers.keys()) >= 1:
                                    if succ_id not in self.block_transfers.keys():
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys() and val2 != 20:  #move up to next available dag (20 used as a max for testing purposes)
                                            val2 = val2 + 1
                                if not early_initialize:
                                    conditional_groups[self.cgid] = []
                                conditional_groups[self.cgid].append(
                                    self.write_cond(self.loop_headers[succ_id]['instr'],
                                                    cgid, [bid], 1,
                                                    [val2],
                                                    self.expid, 1))
                                seen_pair.append((bid, val2))
                                edges_not_translated.remove((bid, succ_id))
                                if 'w' in str(self.program.functions['main']['blocks'][succ_id].label): #if while, needs another edge
                                    val2 = val2 + 1
                                    while val2 not in self.block_transfers.keys() and val2 != 20:
                                        val2 = val2 + 1
                                    if (bid, val2) not in seen_pair:
                                        conditional_groups[self.cgid].append(
                                            self.write_cond(self.loop_headers[succ_id]['instr'],
                                                            cgid, [bid], 1,
                                                            [val2],
                                                            self.expid, 1))
                                        seen_pair.append((bid, val2))
                                self.cgid += 1
                            elif self.loop_headers[succ_id]['t'] is None: #case of non active dag, not from the first block transfer
                                val2 = succ_id
                                if len(self.block_transfers.keys()) >= 1:
                                    if succ_id not in self.block_transfers.keys():
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys() and val2 != 20:
                                            val2 = val2 + 1
                                last = True
                                for l in self.block_transfers[val2]:
                                    if l.type == 'out':
                                        last = False
                                if last: #if last transfer, skip
                                    edges_not_translated.remove((bid, succ_id))
                                    self.cgid += 1
                                    break
                                conditional_groups[self.cgid] = []
                                conditional_groups[self.cgid].append(
                                    self.write_cond(self.loop_headers[succ_id]['instr'],
                                                    cgid, [bid], 1,
                                                    [val2],
                                                    self.expid, 1))
                                seen_pair.append((bid, val2))
                                edges_not_translated.remove((bid, succ_id))
                                self.cgid += 1
                                if edges_not_translated: #remove edges direcly related to this edge
                                    edges = edges_not_translated
                                    edges_to_remove = list()
                                    for e in edges:
                                        if (e[0] == succ_id or e[1] == succ_id) and e[0] < e[1]: #don't want to remove back edges
                                            edges_to_remove.append(e)
                                    for e in edges_to_remove:
                                        edges_not_translated.remove(e)
                                else:
                                    continue
                            else: #otherwise the t path is not none, it's simply not in block transfers, need to find transfers manually
                                transfers = list()
                                for inst in edges_not_translated:
                                    if inst[0] == self.loop_headers[succ_id]['t']:
                                        transfers.append(inst[1])
                                conditional_groups[self.cgid] = []
                                for t in transfers:
                                    if t not in self.block_transfers:
                                        transfers.remove(t)
                                        for inst in edges_not_translated: #append edges to blocks that are active
                                            if inst[0] == t and inst[1] in self.block_transfers:
                                                transfers.append(inst[1])
                                for t in transfers: #for each transfer create a condtional group
                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'],
                                                        cgid, [bid], 1,
                                                        [t],
                                                        self.expid, 1))
                                    seen_pair.append((bid, t))
                                edges_not_translated.remove((bid, succ_id))
                                if edges_not_translated:
                                    #if (succ_id, self.loop_headers[succ_id]['t']) in edges_not_translated: (usually always present)
                                    edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['t']))
                                    self.cgid += 1
                                else:
                                    continue


                            conditional_groups[self.cgid] = []
                            # find all back edges -- this is probably wrong, as these may fall into different CGs (Old warning)
                            iteration = 0
                            prev_val = -1
                            dup = False
                            back_edges = [x for x in edges_not_translated if x[1] is succ_id and x[0] > x[1]]
                            for be in back_edges:
                                if dup and iteration < 2:  # allocate space for the duplicated instructions
                                    conditional_groups[self.cgid] = []
                                iteration += 1
                                val = be[0]
                                if len(self.block_transfers.keys()) >= 1:
                                    if be[0] not in self.block_transfers.keys():
                                        val = val - 1
                                        while val not in self.block_transfers.keys() and val != -1:  # drop down to active dag
                                            val = val - 1
                                if prev_val is val:
                                    val -= 1
                                prev_val = val
                                if val not in self.block_transfers and not no_trans: #if val still not in block transfers, it's not a live dag and should be skipped in the cfg
                                    conditional_groups.pop(self.cgid, None)
                                    edges_not_translated.remove((be[0], succ_id))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    break
                                # ensure cgid groups stay together
                                cgid = self.cgid
                                if val not in self.cgid_pair.keys():
                                    self.cgid_pair[val] = self.cgid
                                else:
                                    check = self.cgid_pair[val]
                                    if check != self.cgid:
                                        cgid = check
                                dup = False
                                # last_block = None
                                if be[0] not in self.block_transfers:  # check the need to duplicate the back edge and out edge for a second conditional (else)
                                    times_to_last_block = 0
                                    for e in edges_not_translated:
                                        if e[1] is be[0]:
                                            times_to_last_block += 1
                                    if times_to_last_block is 2 and iteration < 2:
                                        dup = True
                                        back_edges.append(be)
                                if self.loop_headers[succ_id]['t'] in self.block_transfers or no_trans:
                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                    [val], 1,
                                                    [self.loop_headers[succ_id]['t']],
                                                    self.expid, 1, 'LOOP'))
                                    seen_pair.append((val, self.loop_headers[succ_id]['t']))
                                    edges_not_translated.remove((be[0], succ_id))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[0], succ_id))
                                    if len(self.block_transfers.keys()) >= 1:
                                        if self.loop_headers[succ_id]['f'] not in self.block_transfers.keys():
                                            if (be[1], self.loop_headers[succ_id]['f']) in edges_not_translated:
                                                edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                            elif 'w' in str(self.program.functions['main']['blocks'][succ_id].label) and self.loop_headers[succ_id]['f'] is None: #case for while where f path leads to an inactive dag
                                                transfers4 = list()
                                                for inst in edges_not_translated_save:
                                                    if inst[0] == self.loop_headers[succ_id]['t']:
                                                        transfers4.append(inst[1])
                                                #conditional_groups[self.cgid] = []
                                                for t in transfers4:
                                                    if t not in self.block_transfers:
                                                        transfers4.remove(t)
                                                        for inst in edges_not_translated_save:
                                                            if inst[0] == t:
                                                                transfers4.append(inst[1])
                                                for t in transfers4:
                                                    if (val, t) in seen_pair:
                                                        transfers4.remove(t)
                                                for t in transfers4:
                                                    conditional_groups[self.cgid].append(
                                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                                        [val], 1,
                                                                        [t],
                                                                        self.expid, 1, 'LOOP'))
                                                    seen_pair.append((val, t))
                                            continue

                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                    [val], 1,
                                                    [self.loop_headers[succ_id]['f']],
                                                    self.expid, 1, ))
                                    seen_pair.append((val, self.loop_headers[succ_id]['f']))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[1], self.loop_headers[succ_id]['f']))
                                        self.cgid += 1
                                elif self.loop_headers[succ_id]['t'] is None and bid == next(iter(self.block_transfers)): #for instances of nested conditionals with non active dags such that 't' path is None
                                    val2 = succ_id
                                    if len(self.block_transfers.keys()) >= 1:
                                        if succ_id not in self.block_transfers.keys():
                                            val2 = val2 + 1
                                            while val2 not in self.block_transfers.keys() and val2 != 20:
                                                val2 = val2 + 1
                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [val2],
                                                        self.expid, 1, ))
                                    seen_pair.append((val, val2))
                                    if 'w' in str(self.program.functions['main']['blocks'][val2].label): #if a while, needs extra edge
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys() and val2 != 20:
                                            val2 = val2 + 1
                                        if (val, val2) not in seen_pair:
                                            conditional_groups[self.cgid].append(
                                                self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                                [val], 1,
                                                                [val2],
                                                                self.expid, 1, ))
                                            seen_pair.append((val, val2))
                                    edges_not_translated.remove((be[0], succ_id))
                                    if len(self.block_transfers.keys()) >= 1:
                                        if self.loop_headers[succ_id]['f'] not in self.block_transfers.keys():
                                            if (be[1], self.loop_headers[succ_id]['f']) in edges_not_translated:
                                                edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                            continue

                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1, ))
                                    seen_pair.append((val, self.loop_headers[succ_id]['f']))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[1], self.loop_headers[succ_id]['f']))
                                        self.cgid += 1
                                elif self.loop_headers[succ_id]['t'] is None: #when a certain edge is missing (repeat)
                                    if (val, val2) not in seen_pair:
                                        conditional_groups[self.cgid].append(
                                            self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [val2],
                                                        self.expid, 1, ))
                                        seen_pair.append((val, val2))
                                    if 'w' in str(self.program.functions['main']['blocks'][val2].label): #if a while, needs extra edge
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys() and val2 != 20:
                                            val2 = val2 + 1
                                        if (val, val2) not in seen_pair:
                                            conditional_groups[self.cgid].append(
                                                self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                                [val], 1,
                                                                [val2],
                                                                self.expid, 1, ))
                                            seen_pair.append((val, val2))
                                    edges_not_translated.remove((be[0], succ_id))
                                    if len(self.block_transfers.keys()) >= 1:
                                        if self.loop_headers[succ_id]['f'] not in self.block_transfers.keys():
                                            if (be[1], self.loop_headers[succ_id]['f']) in edges_not_translated:
                                                edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                            continue
                                    self.cgid += 1
                                else: #create conditional groups for the previously found transfers
                                    for t in transfers:
                                        conditional_groups[self.cgid].append(
                                            self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [t],
                                                        self.expid, 1, 'LOOP'))
                                        seen_pair.append((val, t))
                                    if len(transfers) == 0: #if transfers are empty
                                        val3 = self.loop_headers[succ_id]['t']
                                        while val3 not in self.block_transfers.keys() and val3 != -1:
                                            val3 = val3 - 1
                                        if val3 != 0 and (val, val3) not in seen_pair:
                                            conditional_groups[self.cgid].append(
                                                self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                                [val], 1,
                                                                [val3],
                                                                self.expid, 1, 'LOOP'))
                                            seen_pair.append((val, val3))
                                    edges_not_translated.remove((be[0], succ_id))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[0], succ_id))
                                    if len(self.block_transfers.keys()) >= 1:
                                        if self.loop_headers[succ_id]['f'] not in self.block_transfers.keys():
                                            if (be[1], self.loop_headers[succ_id]['f']) in edges_not_translated:
                                                edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                            continue

                                    conditional_groups[self.cgid].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1, ))
                                    seen_pair.append((val, self.loop_headers[succ_id]['f']))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[1], self.loop_headers[succ_id]['f']))
                                        self.cgid += 1


                            # deal with exit from loop (Old method, handled elsewhere)
                            # check if this assay has TDs, if not, act normal, if so, change behavior of exits
                            # if self.loop_headers[succ_id]['t'] in self.block_transfers:
                            # for to in [self.block_transfers[self.loop_headers[succ_id]['t']]]:
                            # for val in self.predecessor_edges:
                            # if val[1] == self.loop_headers[succ_id]['f']:
                            # string_key = 't'
                            # if 2 <= len(self.program.functions[root]['blocks'][val[0]].jumps): #only currently checking if last block, not likely to work in all scenarios
                            # string_key = 't'
                            # conditional_groups[self.cgid].append(
                            # self.write_cond(self.loop_headers[val[0]]['instr'],
                            # self.cgid,
                            # [self.loop_headers[val[0]][string_key]], 1,
                            # [val[1]],
                            # self.expid, 1, ))
                            # edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['f']))
                            self.cgid += 1
                        else:  # dealing with if conditional
                            if cond and executable:
                                self.cblock = block
                                #conditional_groups[self.cgid] = []
                                for instr in self.program.functions['main']['blocks'][bid].instructions:
                                    if instr.op is IRInstruction.CONDITIONAL:
                                        # ensure cgid groups stay together
                                        cgid = self.cgid
                                        if bid not in self.cgid_pair.keys():
                                            self.cgid_pair[bid] = self.cgid
                                        else:
                                            check = self.cgid_pair[bid]
                                            if check != self.cgid:
                                                cgid = check
                                        if cgid == self.cgid:
                                            conditional_groups[self.cgid] = []
                                        conditional_groups[cgid].append(
                                            self.write_cond(self.cfg[bid][instr.iid]['instr'],
                                                            cgid, [bid], 1,
                                                            [self.cfg[bid][instr.iid]['t']],
                                                            self.expid, 1, 'IF'))
                                        seen_pair.append((bid, self.cfg[bid][instr.iid]['t']))
                                        edges_not_translated.remove((bid, self.cfg[bid][instr.iid]['t']))
                                        if self.cfg[bid][instr.iid]['f'] is not None:
                                            skip = False
                                            if self.cfg[bid][instr.iid]['f'] not in self.block_transfers:
                                                skip = True
                                            if skip: #need to manually find transfers
                                                transfers2 = list()
                                                for inst2 in edges_not_translated:
                                                    if inst2[0] == self.cfg[bid][instr.iid]['f']:
                                                        transfers2.append(inst2[1])
                                                #conditional_groups[self.cgid] = []
                                                for t in transfers2:
                                                    if t not in self.block_transfers:
                                                        transfers2.remove(t)
                                                        for inst in edges_not_translated:
                                                            if inst[0] == t:
                                                                transfers2.append(inst[1])
                                                for t in transfers2:
                                                    conditional_groups[self.cgid].append(
                                                        self.write_cond(None,
                                                                        cgid, [bid], 1,
                                                                        [t],
                                                                        self.expid, 1))
                                                    seen_pair.append((bid, t))
                                                edges_not_translated.remove((bid, self.cfg[bid][instr.iid]['f']))
                                                self.cgid += 1
                                                continue
                                            conditional_groups[self.cgid].append(
                                                self.write_cond(self.cfg[bid][instr.iid]['instr'],
                                                                cgid, [bid], 1,
                                                                [self.cfg[bid][instr.iid]['f']],
                                                                self.expid, 1))
                                            seen_pair.append((bid, self.cfg[bid][instr.iid]['f']))
                                            edges_not_translated.remove((bid, self.cfg[bid][instr.iid]['f']))
                                            # self.cgid += 1
                                self.cgid += 1
                            else:  # unconditional exit from an if block
                                # check to see if transfers must be manually found
                                skip = True
                                for to in [self.block_transfers[bid]]:
                                    for to2 in to:
                                        if to2.type is 'out':
                                            skip = False
                                if succ_id not in self.block_transfers:
                                    skip = True
                                if skip:
                                    #conditional_groups[self.cgid] = []
                                    if bid > succ_id:
                                        cgid = self.cgid
                                        if bid not in self.cgid_pair.keys():
                                            self.cgid_pair[bid] = self.cgid
                                        else:
                                            check = self.cgid_pair[bid]
                                            if check != self.cgid:
                                                cgid = check
                                        self.cblock = block
                                        conditional_groups[self.cgid] = []
                                        transfers3 = list()
                                        for e in edges_not_translated_save:
                                            if e[0] == succ_id:
                                                for e1 in edges_not_translated_save:
                                                    if e1[0] == e[1]:
                                                        transfers3.append(e1[1])
                                        t_to_remove = list()
                                        for e in transfers3:
                                            if e not in self.block_transfers:
                                                t_to_remove.append(e)
                                                for inst in edges_not_translated_save:
                                                    if inst[0] == e:
                                                        transfers3.append(inst[1])
                                        for e in t_to_remove:
                                            transfers3.remove(e)
                                        for t in transfers3:
                                            conditional_groups[self.cgid].append(
                                                self.write_cond(None,
                                                                cgid, [bid], 1,
                                                                [t],
                                                                self.expid, 1))
                                            seen_pair.append((bid, t))
                                        self.cgid += 1
                                        edges_not_translated.remove((bid, succ_id))
                                        continue
                                    else:
                                        self.cgid += 1
                                        edges_not_translated.remove((bid, succ_id))
                                        continue
                                # ensure cgid groups stay together
                                cgid = self.cgid
                                if bid not in self.cgid_pair.keys():
                                    self.cgid_pair[bid] = self.cgid
                                else:
                                    check = self.cgid_pair[bid]
                                    if check != self.cgid:
                                        cgid = check
                                self.cblock = block
                                conditional_groups[self.cgid] = []
                                conditional_groups[self.cgid].append(
                                    self.write_cond(None,
                                                    cgid, [bid], 1,
                                                    [succ_id],
                                                    self.expid, 1))
                                seen_pair.append((bid, succ_id))
                                edges_not_translated.remove((bid, succ_id))
                                self.cgid += 1
                else: #not an active dag, remove edges directly connected to it
                    edges = list()
                    for e in edges_not_translated:
                        if e[0] == bid:
                            edges.append(e)
                    for e in edges:
                        edges_not_translated.remove(e)

        return conditional_groups

    def transform(self):
        self.build_cfg()
        for root in self.program.functions:
            self.root = root
            exp_name = self.config.input.rsplit('/', 1)[1][:-3]  # get file input name -'.bs'
            cfg_file = open("%s/%s.cfg" % (self.config.output, exp_name), "w")
            cfg_file.write("NAME(%s.cfg)\n\n" % exp_name)

            # conditional groups
            cgs = dict()

            for bid, block in sorted(self.program.functions[root]['blocks'].items()):
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

                cfg_file.write("DAG(DAG%s)\n" % str(bid))

                dag_file = open("%s/%s_DAG%s.dag" % (self.config.output, exp_name, str(bid)), "w")
                dag_file.write("DagName (DAG%s)\n" % str(bid))

                # for all uses without defs, we must transfer in
                already_transferred_in = dict()
                dispenses = set()
                for node in block.instructions:
                    if node.name in ['DISPENSE']:
                        dispenses.add(node.defs['var'].points_to.name)
                for node in block.instructions:

                    if node.name in ['PHI', 'BINARYOP', 'CONDITIONAL', 'DISPENSE', 'MATH']: #added PHI
                        continue

                    # for each use, we must check if predecessors in this block defined it
                    #  if no def from predecessor in this block, then must transfer in
                    for use in node.uses:
                        tn = None
                        if type(use['var'].value) in {Module}:
                            continue
                        use = use['var']
                        if isinstance(use, RenamedSymbol):
                            points_to = use.points_to.name
                        else:
                            points_to = use.name
                        # points_to = use.name
                        if points_to in dispenses or points_to in already_transferred_in:
                            continue
                        if use.name not in block.defs:
                            already_transferred_in[points_to] = True
                            dag_file.write(self.write_transfer(self.tid, points_to, False))
                            dag_file.write(self.write_edge(self.tid, node.iid))
                            tn = TransferNode(self.tid, bid, points_to, 'in')
                            block.defs.add(use.name)
                            self.tid += 1
                        if tn is not None:
                            if bid in self.block_transfers:
                                self.block_transfers[bid].add(tn)
                            else:
                                self.block_transfers[bid] = {tn}

                for a, b in self.live_droplets: #transfer live droplets if necessary
                    if b in dispenses or b in already_transferred_in:
                        continue
                    if b not in block.defs:
                        already_transferred_in[b] = True
                        dag_file.write(self.write_transfer(self.tid, b, False))
                        tn = TransferNode(self.tid, bid, b, 'in')
                        d = self.tid
                        self.tid += 1
                        dag_file.write(self.write_edge(d, self.tid))
                        dag_file.write(self.write_transfer(self.tid, b, True))
                        tn2 = TransferNode(self.tid, bid, b, 'out')
                        self.tid += 1
                        if tn is not None:
                            if bid in self.block_transfers:
                                self.block_transfers[bid].add(tn)
                            else:
                                self.block_transfers[bid] = {tn}
                        if tn2 is not None:
                            if bid in self.block_transfers:
                                self.block_transfers[bid].add(tn2)
                            else:
                                self.block_transfers[bid] = {tn2}


                for node in block.instructions:
                    self.opid = node.iid

                    if node.op is IRInstruction.DETECT:
                        dag_file.write(self.write_detect(node))
                    elif node.op is IRInstruction.MIX:
                        dag_file.write(self.write_mix(node))
                    elif node.op is IRInstruction.SPLIT:
                        dag_file.write(self.write_split_helper(node))
                        self.split_offset = list()
                        self.curr_split_offset = list()
                    elif node.op is IRInstruction.HEAT:
                        dag_file.write(self.write_heat(node))
                    elif node.op is IRInstruction.DISPOSE:
                        dag_file.write(self.write_dispose(node))
                    elif node.op is IRInstruction.DISPENSE:
                        dag_file.write(self.write_dispense(node))
                    elif node.op is IRInstruction.PHI or node.op is IRInstruction.CONDITIONAL or node.op is IRInstruction.MATH or node.op is IRInstruction.NOP:
                        continue
                    else:
                        if self.config.debug:
                            self.log.warning("Unrecognized/unsupported instruction type: %s" % node.name)

                # this is a bit of a hack, because SSA renaming doesn't quite work how we might hope for heats/detects
                # for all defs without uses, we must transfer out (if used elsewhere)
                #   or dispose (if never used again) (Old)

                # For now, for each rdef in the block, we get the original variable name (_def) and instruction (i)
                #  Then, we check if rdef is used in the block (we do not need to transfer) AFTER this instruction
                #    if not, we check each successor block (succ): for each instruction si in succ, we check
                #    if their uses points to _def, if so, we must transfer.
                for rdef in block.defs:
                    _def = None
                    skip = False
                    defIndex = -1
                    for index in range(len(block.instructions)):
                        i = block.instructions[index]
                        if i.name in ['PHI', 'BINARYOP', 'CONDITIONAL', 'DISPOSE', 'MATH', 'NOP', 'DETECT']:
                            skip = True
                            continue
                        if defIndex == -1:
                            if rdef is i.defs['name']:
                                defIndex = index
                                skip = False
                                # find the points_to def
                                _def = i.defs['var'].points_to.name
                                instr = i
                                break
                            continue

                    # after finding the definition point, we traverse in reverse order to find the
                    #  last use.  if it is not used after define, or if the last use is a detect/heat, we must transfer
                    for index in reversed(range(len(block.instructions))):
                        if index == defIndex:
                            break
                        i = block.instructions[index]
                        # heat and detects use the droplet, but do not consume it, so may need to transfer still
                        if i.name in ['HEAT', 'DETECT'] and rdef in [x['name'] for x in i.uses]:
                            instr = i
                            skip = False
                            if _def is None:
                                x = [x for x in i.uses if x['name'] == rdef]
                                _def = x[0]['var'].points_to.name
                            break
                        if i.name == 'PHI': #move along if phi
                             continue
                        x = [x for x in i.uses if x['name'] == rdef]
                        if x:  # we use this variable after it is defined in this block
                            skip = True
                            break

                    if skip:
                        continue

                    transferred = False
                    tn = None
                    # we've made it here, we must transfer this rdef

                    def transfer_(trans):
                        tn = None   #tn must be defined
                        try:
                            reachable = (
                                {x for v in dict(nx.bfs_successors(self.cfg['graph'], bid)).values() for x in v})
                        except nx.NetworkXError as e:
                            # self.log.warning("Droplet {} is not being disposed or saved.".format(_def))
                            return trans
                        for s in reachable:
                            if trans:
                                break
                            # get successor block
                            sblock = self.program.functions[root]['blocks'][s]
                            for si in sblock.instructions:
                                if si.op in {IRInstruction.PHI, IRInstruction.CONDITIONAL, IRInstruction.NOP}: #added NOP
                                    continue
                                if trans:
                                    break
                                #for t in si.uses: (old)
                                    #x = t['name']
                                if si.name is 'DISPENSE':
                                    x = si.uses[0]['name']
                                else:
                                    x = [x['var'].points_to.name for x in si.uses if type(x['var']) is not Symbol]  #x = si.uses[len(si.uses) -1]['var'].points_to.name (old method)
                                if _def in x:
                                    dag_file.write(self.write_edge(instr.iid, self.tid))
                                    dag_file.write(self.write_transfer(self.tid, _def, True))
                                    tn = TransferNode(self.tid, bid, _def, 'out')
                                    self.live_droplets.append((bid, _def))
                                    self.tid += 1
                                    trans = True
                                    break
                        if tn is not None:
                            if bid in self.block_transfers:
                                self.block_transfers[bid].add(tn)
                            else:
                                self.block_transfers[bid] = {tn}
                        return trans

                    if block.dag is not None:
                        # list of reachable block ids
                        transferred = transfer_(transferred)

                    else:
                        transferred = True
                    if not transferred:  # what to do with this droplet?
                        if self.config.debug:
                            self.log.warning(
                                "No more operations for {}, warning will appear in {}".format(_def, dag_file.name))
                        dag_file.write("// **NO MORE OPERATIONS FOR {}; SHOULD SAVE OR DISPOSE**".format(_def))
                    if tn is not None:
                        if bid in self.block_transfers:
                            self.block_transfers[bid].add(tn)
                        else:
                            self.block_transfers[bid] = {tn}

                dag_file.close()
                self.num_dags += 1

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

            # see create_conditional_groups

            edges_not_translated = list(nx.edges(self.cfg['graph']))

            conditional_groups = self.create_conditional_groups(edges_not_translated)


            #self.num_cgs = conditional_groups.__len__() (old method)
            self.num_cgs = len(self.cgid_pair)
            cfg_file.write("\nNUMCGS(%s)\n\n" % self.num_cgs)

            for cg in conditional_groups.values():
                for val in cg:
                    cfg_file.write(val)

            cfg_file.close()

        return True

    def write_branch(self) -> str:
        pass

    def write_expression(self) -> str:
        pass
