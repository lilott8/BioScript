import networkx as nx
from collections import defaultdict

from compiler.data_structures import IRInstruction
from compiler.data_structures import RelationalOps
from compiler.data_structures.ir import Conditional
from compiler.data_structures.variable import *
from compiler.targets.base_target import BaseTarget
from compiler.data_structures.ir import TempConstraint
from compiler.data_structures.ir import TimeConstraint
from compiler.data_structures.ir import UseIn, UseInType
import math
from io import StringIO
import os

# TODO determine IR for pre-compiled functions

# TODO need to transfer all live droplets OVER function call blocks to all of the FC's successors


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

    def __init__(self, program, test=False):
        super().__init__(program, "MFSimTarget")
        self.test = test
        self.cblock = None
        self.opid = None
        self.root = None
        self.edges_not_translated = None
        self.predecessor_edges = list()
        self.cgid = defaultdict(lambda: 0)
        self.expid = 0
        self.cfg = dict()
        self.block_transfers = dict()
        self.loop_headers = dict()
        self.scope_variable = list()
        #for split semantics and live droplet tracking
        self.cgid_pair = defaultdict(lambda: dict())  # to ensure cgid stay consistent
        self.live_droplets = list()  # to ensure droplets are passed along accoringly
        self.split_offset = list()  # for split recursion
        self.curr_split_offset = list()  # for split recursion
        self.last_split_size = list()  # for SIMD instructions following splits
        # for generating usein constraints in json file, dictionaries and lists
        self.constraints = []
        self.dot_file = None
        self.useins = []
        self.usein_data = {"constraints": self.constraints}
        self.usein_subdata = {"useins": self.useins}
        self.root = None
        self.is_function = False

        if not self.config.output:
            self.log.fatal("MFSim target requires an output path to be specified. Include \"-o <path/to/output/>\" in arguments list.")
            exit(-1)
        self.output_path = self.config.output + '/' + self.config.input.rsplit('/', 1)[1][:-3]
        os.makedirs(self.output_path, exist_ok=True)
        splits = 0
        for fun in program.functions.values():
            for bb in fun['blocks'].values():
                for i in bb.instructions:
                    if i.op is IRInstruction.SPLIT:
                        splits += i.split_size
        enter = next(iter(self.program.functions['main']['blocks']))  # updated from self.program.entry_point
        self.tid = int(math.ceil((self.program.functions['main']['blocks'][enter].instructions[0].id_counter + 1 + splits) / 100.0)) * 100
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
        self.num_calls = 0
        self.num_returns = 0

    def build_cfg(self):
        for root in self.program.functions:
            self.root = root
            if self.program.config.inline:  # inline timesave
                if root in self.program.symbol_table.functions:
                    continue
            leafs = set()
            tags = dict()
            self.dags[root] = dict()
            self.cfg[self.root] = dict()
            self.cfg[self.root]['graph'] = nx.DiGraph()
            remove_nodes = set()
            remove_edges_from = set()

            for bid, block in self.program.functions[root]['blocks'].items():
                if not block.instructions:
                    # attach edges from pred to succ
                    for pid in self.program.functions[root]['graph'].predecessors(bid):
                        for sid in self.program.functions[root]['graph'].successors(bid):
                            self.cfg[self.root]['graph'].add_edge(pid, sid)
                    # add bid to the list of nodes that must have all edges removed from final graph
                    remove_nodes.add(bid)
                    continue
                if not self.program.config.inline:  # Don't need this when inlining
                    try:
                        for sid in self.program.functions[root]['graph'].successors(bid):
                           self.cfg[self.root]['graph'].add_edge(bid, sid)
                    except nx.NetworkXError as e:
                        pass
                self.cfg[self.root][bid] = dict()
                curr = self.cfg[self.root][bid]
                write = True
                dag = nx.DiGraph()
                for instruction in block.instructions:
                    if instruction.op is IRInstruction.NOP:
                        continue

                    # deal with conditionals
                    if instruction.op is IRInstruction.CONDITIONAL:

                        if len(block.instructions) == 1:
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
                    #  non-conditionals
                    elif hasattr(instruction, 'uses'):
                        # Case x = op y (dispense, heat, dispose, store)
                        if len(instruction.uses) == 1:
                            # Look at the r-value.
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

                if write:
                    self.program.functions[root]['blocks'][bid].dag = dag
                    self.dags[root][bid] = dag
                else: # conditional all by its lonesome self -- must have had a function call just prior
                    last_dag = [x for x in self.program.bb_graph.predecessors(bid)][0]
                    self.program.functions[root]['blocks'][last_dag].add(instruction)
                    self.cfg[self.root][last_dag] = curr

            for remove in remove_nodes:
                if remove in self.cfg[self.root]['graph'].nodes:
                    self.cfg[self.root]['graph'].remove_node(remove)

            for remove in remove_edges_from:
                succ = list(self.cfg[self.root]['graph'].successors(remove))
                for s in succ:
                    self.cfg[self.root]['graph'].remove_edge(remove, s)

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
        check = instr.uses[0]['name']
        found_instr = False
        for i in self.cblock.instructions:
            if i is instr:
                found_instr = True
                continue
            if not found_instr:
                continue
            if i.op in {IRInstruction.NOP, IRInstruction.CONDITIONAL}:
                continue
            if instr.op is IRInstruction.DETECT:  # Note: detect is looking for uses rather than defs
                for use in i.uses:
                    if use['name'] in uses:
                        if i.iid != check:
                            if instr.uses[1]['name'] == use['name'] and instr.uses[1]['offset'] == use['offset']:
                                if not _ret:
                                    # TODO check use vs i.defs
                                    # _ret.append(i.defs['name'])
                                    _ret.append(use['name'])
            else:
                if i.defs['name'] in uses:  # this instruction is one of the uses
                    if i.iid != check:
                        for u in i.uses:
                            if u['name'] == instr.defs['name'] and u['offset'] == instr.defs['offset']:
                                if not _ret:
                                    _ret.append(i.defs['var'].name)

        if len(_ret) < 1:
            self.log.fatal("A non-split instruction has multiple successors!")
            exit(-1)

        return _ret

    def write_transfer(self, id, name, out=False, param=False) -> str:
        self.num_transfers += 1
        return "NODE (%s, %s, %s)\n" % (str(id), "TRANSFER_OUT" if out else "PARAM" if param else "TRANSFER_IN", name)

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
              An MFSim MIX node has 5 to 7 parameters:
              nodeid, "MIX", number of input drops, time, <useinseconds>, <useintype>, mixName
              number of input drops must be >= 2
              mixName from [Mix, Vortex, Tap, Invert, Suspend, Stir]  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = f'NODE ({self.opid}, MIX, '

        time = 10
        usein_time = -1
        usein_type = UseInType.SLE
        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
            if type(t) is UseIn:
                usein_time = t.quantity
                usein_type = t.useinType

        self.dot_file.write("\n {} [label=\"mix({}s)\" fillcolor=\"#99 D5 CA\", style=filled];".format(self.opid, int(time)))

        _ret += "2, {}, ".format(str(time))

        if usein_time > -1:
            _ret += "{}, ".format("{}, {}".format(usein_time, "{}".format(usein_type.name)))

        _ret += "{})\n".format(instr.defs['var'].points_to.name)

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
                    to = list()
                    to.append(instr.defs['var'].points_to.name)
                    break
                break

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)
            to = list(dict.fromkeys(to))  # remove potential duplicates and keep order

        for key in to:
            to_instr = []
            found_instr = False
            offset = 0
            set_offset = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if offset > 0:
                    offset -= 1
                    continue
                if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH, IRInstruction.CONDITIONAL}:
                    if x.defs['var'].name == key:
                        if not set_offset and self.last_split_size == x.defs['size'] and (x.defs['offset'] == instr.defs['offset'] + 1 or x.defs['offset'] == 0 and instr.defs['offset'] == self.last_split_size - 1):
                            n = x.defs['size']
                            ex_of_2 = True
                            while n != 1 and n > 1:
                                if n % 2 != 0:
                                    ex_of_2 = False
                                n = n / 2
                            if ex_of_2:
                                offset = x.defs['size'] - 2
                                set_offset = True
                                continue
                        to_instr.append(x)
                        break

            for ti in to_instr:
                if ti.iid == self.opid:
                    continue
                _ret += self.write_edge(self.opid, ti.iid)
                self.dot_file.write("\n{} -> {}{};".format(self.opid, ti.iid, "" if usein_time == -1 else " [ label=\"{} {}\" ]".format(usein_type.name, usein_time)))
                break

        for key in to:
            if hasattr(instr.defs['var'], 'points_to'):  # ensure we grab the existing name
                to_instr = [x for x in self.cblock.instructions if x.defs and x.defs['var'].points_to.name is key]
            else:
                to_instr = [x for x in self.cblock.instructions if x.defs and x.defs['var'].name is key]
            for ti in to_instr:
                if ti.iid == self.opid:
                    continue
                _ret += self.write_edge(self.opid, ti.iid)
                self.dot_file.write("\n{} -> {}{};".format(self.opid, ti.iid, "" if usein_time == -1 else " [ label=\"{} {}\" ]".format(usein_type.name, usein_time)))
                break

        self.num_mixes += 1
        return _ret

    def write_split_helper(self, instr):
        """
                      Helper function for split recursion
                :param instr:
                :return: chain of all splits as a str:
                """
        self.last_split_size = deepcopy(instr.split_size)
        if instr.split_size == 2:
            _ret = self.write_split(instr)
            return _ret

        else:
            _ret = "NODE (%s, SPLIT, " % str(self.opid)

            self.dot_file.write("\n {} [label=\"split\" fillcolor=\"#99 D2 F2\", style=filled];".format(self.opid))

            numDrops = 2
            time = 2

            for t in instr.meta:  # has no purpose as split's do not have time metadata
                if type(t) is TimeConstraint:
                    time = t.quantity
                    break

            n = instr.split_size
            offset = n/2

            _ret += "%s, %s, SPLIT)\n" % (str(numDrops), str(time))
            _ret += self.write_edge(self.opid, self.opid + 1)
            self.dot_file.write("\n{} -> {};".format(self.opid, self.opid + 1))
            _ret += self.write_edge(self.opid, self.opid + int(offset))
            self.dot_file.write("\n{} -> {};".format(self.opid, self.opid + int(offset)))
            self.num_splits += 1

            valid = True
            while n != 1 and n > 1:
                if n % 2 != 0:
                    valid = False
                n = n / 2

            if not valid:
                self.log.fatal("A split instruction has an invalid number of successors!")
                exit(-1)
            else:  # number is valid 2, 4, 8, ect, continue
                # handle left and right sides
                left_instr = deepcopy(instr)
                left_instr.split_size = instr.split_size/2
                left_instr.id_counter += 1
                left_instr.iid += 1
                left_instr.defs['size'] = left_instr.defs['size']/2
                self.opid += 1
                hold_left_and_right = self.write_split_helper(left_instr)
                right_instr = deepcopy(left_instr)
                right_instr.id_counter += 1
                right_instr.iid += 1
                self.opid += 1
                hold_left_and_right += self.write_split_helper(right_instr)
                _ret += hold_left_and_right
                self.last_split_size = deepcopy(instr.split_size)
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

        self.dot_file.write("\n {} [label=\"split\" fillcolor=\"#99 D2 F2\", style=filled];".format(self.opid))

        # Default time value is expected, and num drops in mfsim is always required to be exactly 2
        # exponentials of 2 (4,8,16) etc handled in split helper
        #TODO: Splits currently are treated as breaking a dropplet directly in half at each split.
        # as such mfsim currently expects total splits to be a factor of 2
        # in the future, this may not always be the case. In such a scenario, odd numbered sized splits,
        # and splits in which the volume varies in each subsequent dropplet may vary, rather than just half

        numDrops = 2
        time = 2

        for t in instr.meta:  # has no purpose as split intructions have no time metadata
            if type(t) is TimeConstraint:
                time = t.quantity
                break

        _ret += "%s, %s, %s)\n" % (str(numDrops), str(time), instr.defs['var'].name)

        to = list(self.cblock.dag.successors(instr.defs['var'].name))
        to = [x for x in to if x == instr.defs['name']]

        if len(to) == 0 and len(list(self.cblock.dag.successors(instr.defs['var'].name))) >= 1:
            to = [instr.defs['name']]

        for key in to:
            to_instr = []
            counter = 0
            while counter != 2:
                found_instr = False
                for x in self.cblock.instructions:
                    if x.name in {'NOP', 'PHI'}:
                        continue
                    if x.uses[0]['name'] == instr.uses[0]['name'] and x.name == 'SPLIT':
                        found_instr = True
                        continue
                    if not found_instr:
                        continue
                    if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH}:
                        for y in x.uses:
                            if y['var'].name == key:
                                if y['offset'] in self.split_offset or counter == 2:
                                    continue
                                if len(self.curr_split_offset) == 0:
                                    if y['offset'] == 0:
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
                self.dot_file.write("\n{} -> {};".format(self.opid, ti.iid))

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

        time = 10

        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
                break

        self.dot_file.write("\n {} [label=\"detect({}s)\" fillcolor=\"#D1 BC D2\", style=filled];".format(self.opid, int(time)))
        _ret += "%s, %s(%s))\n" % (str(time), instr.defs['var'].points_to.name, instr.uses[1]['var'].points_to.name)

        to = list(self.cblock.dag.successors(instr.uses[1]['name']))
        to = [x for x in to if x != instr.defs['name']]

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)
            to = list(dict.fromkeys(to))  # remove potential duplicates and keep order

        for key in to:
            to_instr = []
            found_instr = False
            offset = 0
            set_offset = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if offset > 0:
                    offset -= 1
                    continue
                if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH, IRInstruction.CONDITIONAL}:
                    y = x.defs
                    if y['var'].name == key:
                        if not set_offset and self.last_split_size == y['size'] and (y['offset'] == instr.uses[1]['offset'] + 1 or y['offset'] == 0 and instr.uses[1]['offset'] == self.last_split_size - 1):
                            n = y['size']
                            ex_of_2 = True
                            while n != 1 and n > 1:
                                if n % 2 != 0:
                                    ex_of_2 = False
                                n = n / 2
                            if ex_of_2:
                                offset = y['size'] - 2
                                set_offset = True
                                continue
                        to_instr.append(x)
                        break

            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)
                self.dot_file.write("\n{} -> {};".format(self.opid, ti.iid))
                break

        self.num_detects += 1
        return _ret

    def write_heat(self, instr) -> str:
        """
             An MFSim HEAT node has 4 to 6 parameters:
                  nodeid, "HEAT", time, <usein seconds>, <usein_type>, nodeName
                  nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = "NODE (%s, HEAT, " % str(self.opid)

        time = 10
        usein_time = -1
        usein_type = UseInType.SLE

        temp = 30
        for t in instr.meta:
            if type(t) is TimeConstraint:
                time = t.quantity
            if type(t) is UseIn:
                usein_time = t.quantity
                usein_type = t.useinType
            if type(t) is TempConstraint:
                temp = t.quantity

        self.dot_file.write("\n {} [label=\"heat({}s)\" fillcolor=\"#FF C3 74\", style=filled];".format(self.opid, int(time)))

        _ret += "{}, ".format(str(time))

        if usein_time > -1:
            _ret += "{}, ".format("{}, {}".format(usein_time, "{}".format(usein_type.name)))

        _ret += "{}, {})\n".format(instr.uses[0]['var'].points_to.name, temp)

        to = list(self.cblock.dag.successors(instr.defs['var'].name))

        if len(to) > 1:
            found_instr = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr or x.op in [IRInstruction.NOP]:
                    continue
                if x.defs['var'].name == instr.defs['var'].name:
                    to = list()
                    to.append(instr.defs['var'].name)
                    break
                break

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)
            to = list(dict.fromkeys(to))  # remove potential duplicates and keep order

        for key in to:
            to_instr = []
            found_instr = False
            offset = 0
            set_offset = False
            for x in self.cblock.instructions:
                if x is instr:
                    found_instr = True
                    continue
                if not found_instr:
                    continue
                if offset > 0:
                    offset -= 1
                    continue
                if x.op not in {IRInstruction.NOP, IRInstruction.PHI, IRInstruction.DISPENSE, IRInstruction.MATH, IRInstruction.CONDITIONAL}:
                    if x.defs['var'].name == key:
                        if not set_offset and self.last_split_size == x.defs['size'] and (x.defs['offset'] == instr.defs['offset'] + 1 or x.defs['offset'] == 0 and instr.defs['offset'] == self.last_split_size - 1):
                            n = x.defs['size']
                            ex_of_2 = True
                            while n != 1 and n > 1:
                                if n % 2 != 0:
                                    ex_of_2 = False
                                n = n / 2
                            if ex_of_2:
                                offset = x.defs['size'] - 2
                                set_offset = True
                                continue
                        to_instr.append(x)
                        break

            for ti in to_instr:
                if ti.iid == self.opid:
                    continue
                _ret += self.write_edge(self.opid, ti.iid)
                self.dot_file.write("\n{} -> {}{};".format(self.opid, ti.iid, "" if usein_time == -1 else " [ label=\"{} {}\" ]".format(usein_type.name, usein_time)))
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

        # if self.config.architecture == 'opendrop':
        #     io = 'TCC'
        # else:
        #     io = ''

        if hasattr(instr.uses[0]['var'], 'points_to'):  # ensure we grab the existing name
            _ret = f"NODE ({self.opid}, OUTPUT, null, {instr.uses[0]['var'].points_to.name})\n"  # , {io})\n"
        else:
            _ret = f"NODE ({self.opid}, OUTPUT, null, {instr.uses[0]['var'].name})\n"  # , {io})\n"

        self.dot_file.write("\n {} [label=\"output\" shape=plaintext];".format(self.opid))

        # # TODO for split droplets, need to make sure we're only killing whichever is disposed
        # live_drops = list(self.live_droplets)  # kill droplet
        # for a, b in live_drops:
        #     if hasattr(instr.uses[0]['var'], 'points_to'):  # ensure we grab the existing name
        #         if b == instr.uses[0]['var'].points_to.name:
        #             self.live_droplets.remove((a, b))
        #     else:
        #         if b == instr.uses[0]['var'].name:
        #             self.live_droplets.remove((a, b))

        # DISPOSE for mfsim requires the sinkname and type (drain, save, etc)
        # Only needed for archfile, defaults are fine

        self.num_dispose += 1
        return _ret

    def write_call(self, instr) -> str:
        """
        An MFSim FUNCTION_CALL node has 4 parameters:
            nodeid, type, functionName, nodeName
            nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = f"NODE ({self.opid}, FUNCTION_CALL, {instr.name}, "

        self.dot_file.write("\n {} [label=\"call_{}\" shape=plaintext];".format(self.opid, instr.name))

        if hasattr(instr.defs['var'], 'points_to'):  # ensure we grab the existing name
            _ret += f"{instr.defs['var'].points_to.name})\n"
        else:
            _ret += f"{instr.defs['var'].name})\n"

        to = list(self.cblock.dag._succ[instr.defs['var'].name])

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)

        for key in to:
            to_instr = [x for x in self.cblock.instructions if x.defs is not None and x.defs['var'].name is key]
            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)
                self.dot_file.write("\n{} -> {};".format(self.opid, ti.iid))

        self.num_calls += 1
        return _ret

    def write_return(self, instr) -> str:
        """
        An MFSim RETURN (from function) node has 3 parameters:
              nodeid, type, nodeName
              nodeName  <- this means nothing to MFSim
        :param instr:
        :return:
        """
        _ret = f"NODE ({self.opid}, RETURN, "

        self.dot_file.write("\n {} [label=\"return\" shape=plaintext];".format(self.opid))

        if hasattr(instr.defs['var'], 'points_to'):  # ensure we grab the existing name
            _ret += f"{instr.defs['var'].points_to.name})\n"
        else:
            _ret += f"{instr.defs['var'].name})\n"

        self.num_returns += 1

        # consider this to no longer be a live droplet, for purposes of transfers
        # live_drops = list(self.live_droplets)  # kill droplet
        # for a, b in live_drops:
        #     if hasattr(instr.uses[0]['var'], 'points_to'):  # ensure we grab the existing name
        #         if b == instr.uses[0]['var'].points_to.name:
        #             self.live_droplets.remove((a, b))
        #     else:
        #         if b == instr.uses[0]['var'].name:
        #             self.live_droplets.remove((a, b))
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

        self.dot_file.write("\n {} [label=\"{}\" shape=plaintext];".format(self.opid, instr.uses[0]['name']))

        capture = instr.defs['var'].volumes
        volume = next(iter(capture.values()))

        # if self.config.architecture == 'opendrop':
        #     io = ', TCC'
        # else:
        #     io = ''

        if hasattr(instr.defs['var'], 'points_to'):  # ensure we grab the existing name
            _ret += f"{instr.uses[0]['name']}, {volume}, {instr.defs['var'].points_to.name})\n"  # {io})\n"
        else:
            _ret += f"{instr.uses[0]['name']}, {volume}, {instr.defs['var'].name})\n"  # {io})\n"

        to = list(self.cblock.dag._succ[instr.defs['var'].name])

        if len(to) > 1:
            to = self.get_dependent_instr(instr, to)

        for key in to:
            to_instr = [x for x in self.cblock.instructions if x.defs is not None and x.defs['var'].name is key]
            for ti in to_instr:
                _ret += self.write_edge(self.opid, ti.iid)
                self.dot_file.write("\n{} -> {};".format(self.opid, ti.iid))

        self.num_dispense += 1
        return _ret

    def write_td(self, from_dag, to_dag) -> str:
        _ret = ""

        if from_dag in self.block_transfers:
            for to in self.block_transfers[from_dag]:
                if to.type == 'out':
                    if to_dag in self.block_transfers:
                        for ti in self.block_transfers[to_dag]:
                            if ti.type == 'in' and ti.name == to.name:
                                _ret += "TD(DAG%s, %s, DAG%s, %s)\n" % (from_dag, to.tid, to_dag, ti.tid)
                elif to.type == 'param':  # and ti.name == to.name:
                    _ret += f"PD(DAG{from_dag}, {to.name}, DAG{to_dag})\n"
                elif to.type == 'ret':
                    _ret += f"RD(DAG{from_dag}, DAG{to_dag}, {to.name})\n"

        _ret += "\n"
        return _ret

    def write_exp(self, cond: Conditional, exp_id: int, from_dag, to_dag, cond_type='UNCOND') -> str:
        _ret = ""

        if cond_type == 'UNCOND':
            _ret += "EXP(%s, " % str(exp_id)
        elif isinstance(cond.right, Conditional):
            # nested conditional
            _ret += "subexpressions\n"
        else:
            _ret += "EXP(%s, " % str(exp_id)

        if cond_type == 'UNCOND':
            _ret += "TRUE, UNCOND, DAG%s)\n" % str(from_dag)
        elif cond_type == 'LOOP':
            if cond.left['name'].startswith('REPEAT'):
                _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(from_dag), int(cond.left['var'].value.value[0]))
            else:  # must be a while
                #    We should translate to a repeat, i.e., i = 0; while (i < 10) { ...i++...} -> repeat 10 times
                #    otherwise, i.e.: x = detect.., while (x...) { x = detect; }, we set up the sensor
                #    reading as the conditional
                # TODO -- if a while is statically known
                #    statically find and save the loop num before translation
                #    currently mfsim_target can only handle i++ or i--
                #    currently cannot factor in e.g.,  i+=2 and operates
                #    by finding the difference between the values of the variable and the constant
                if self.scope_variable == cond.left['var'].name or self.scope_variable == cond.right['var'].name:  # logical while
                    if cond.relop == RelationalOps.LT:  # i = 0 < 10
                        loop_num = abs(cond.right['var'].value.value[0] - cond.left['var'].value.value[0])
                        _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(from_dag), loop_num)
                    elif cond.relop == RelationalOps.GT:  # i = 10 > 0
                        loop_num = abs(cond.left['var'].value.value[0] - cond.right['var'].value.value[0])
                        _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(from_dag), loop_num)
                    elif cond.relop == RelationalOps.LTE:  # i = 0 <= 10
                        loop_num = abs(cond.right['var'].value.value[0] - cond.left['var'].value.value[0]) + 1
                        _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(from_dag), loop_num)
                    elif cond.relop == RelationalOps.GTE:  # i = 10 >= 0
                        loop_num = abs(cond.left['var'].value.value[0] - cond.right['var'].value.value[0]) + 1
                        _ret += "RUN_COUNT, LT, DAG%s, %s)\n" % (str(from_dag), loop_num)
                else:  # fluidic while that needs the conditional to be the sensor value
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
                        cond_v = cond_var['var'].name
                        predes = reversed(list(self.program.functions[self.root]['blocks']))  # find the last def of this variable
                        for p in predes:
                            block = self.program.functions[self.root]['blocks'][p]
                            if cond_v in block.defs:
                                depDag = p
                                for instr in block.instructions:
                                    if instr.defs is not None:
                                        if instr.defs['var'].points_to is cond_var['var'].points_to:
                                            dep_node_id = instr.iid
                                            break
                        if depDag == None:
                            cond_v = str(cond_var['var'].points_to.name) + str((int(cond_v[-1])) + 1)
                            predes = reversed(list(self.program.functions[self.root]['blocks']))
                            for p in predes:
                                block = self.program.functions[self.root]['blocks'][p]
                                if cond_v in block.defs:
                                    depDag = p
                                    for instr in block.instructions:
                                        if instr.defs is not None:
                                            if instr.defs['var'].points_to is cond_var['var'].points_to:
                                                dep_node_id = instr.iid
                                                break

                    for instr in self.cblock.instructions:  # find the source instr
                        if instr.defs is not None:
                            if instr.defs['var'].points_to is cond_var['var'].points_to:
                                dep_node_id = instr.iid
                                break

                    _ret += "ONE_SENSOR, %s, DAG%s, %s, %s)\n" % (
                        relop, str(depDag), str(dep_node_id), float(cond.right['var'].value.value[0]))
        elif cond_type == 'IF':
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
                # hack, assume LOGIC i.e., X < Y, where both X and Y are nums
                _ret += f"LOGIC, {relop}, {float(cond.left['var'].value.value[0])}, {float(cond.right['var'].value.value[0])})\n"

                # self.log.fatal("Could not find a conditional variable")
                # exit(-1)
            else:

                depDag = None
                dep_node_id = -1
                # current block has the definition to this conditional variable
                if cond_var['var'].name in self.cblock.defs:
                    depDag = from_dag
                else:
                    predes = reversed(list(self.program.functions[self.root]['blocks']))  # find the last def of this variable
                    for p in predes:
                        block = self.program.functions[self.root]['blocks'][p]
                        if cond_var['var'].name in block.defs:
                            depDag = p
                            for instr in block.instructions:
                                if instr.defs is not None:
                                    if instr.defs['var'].points_to is cond_var['var'].points_to:
                                        dep_node_id = instr.iid
                                        break

                for instr in self.cblock.instructions:  # find the source instr
                    if instr.defs is not None:
                        if instr.defs['var'].points_to is cond_var['var'].points_to:
                            dep_node_id = instr.iid
                            break

                _ret += "ONE_SENSOR, %s, DAG%s, %s, %s)\n" % (
                relop, str(depDag), str(dep_node_id), float(cond.right['var'].value.value[0]))

        # transfer droplets if necessary
        _ret += self.write_td(from_dag, to_dag)

        self.expid += 1

        return _ret

    def write_cond(self, cond: Conditional, group_num: int, dep_dags, num_branch_dags: int, branch_dags, exp_id: int,
                   num_dep_dags=1, cond_type='UNCOND') -> str:
        _ret = "COND(%s, %s, " % (str(group_num), str(num_dep_dags))
        for dag in dep_dags:
            _ret += "DAG%s, " % dag

        _ret += "%s, " % str(num_branch_dags)

        for dag in branch_dags:
            _ret += "DAG%s, " % dag

        _ret += "%s)\n" % str(exp_id)

        # build expression(s)
        if cond_type == 'UNCOND':
            _ret += self.write_exp(cond, exp_id, dep_dags[0], branch_dags[0])
        elif cond_type == 'LOOP':
            _ret += self.write_exp(cond, exp_id, dep_dags[0], branch_dags[0], 'LOOP')
        elif cond_type == 'IF':
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
                    if c.type in ['out', 'param', 'ret']:
                        no_trans = False

        while len(edges_not_translated) > 0:
            for bid, block in self.program.functions[self.root]['blocks'].items():
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
                        if instr.name == 'CONDITIONAL':
                            cond = True
                        if instr.op in [IRInstruction.MIX, IRInstruction.DISPENSE, IRInstruction.DISPOSE,
                                    IRInstruction.HEAT, IRInstruction.SPLIT, IRInstruction.DETECT,
                                    IRInstruction.CALL, IRInstruction.RETURN]:
                            executable = True

                    # deal with successor loop headers, which will take care of [current : translated]:
                    #   bid->succ               :   bid->true
                    #   succ->true              :   [no translation]
                    #   succ->false             :   true->false
                    #   back-edge(s) to succ    :   back1->true...backn->true
                    for succ_id in self.cfg[self.root]['graph'].successors(bid):
                        # we know there is an edge from bid to succ_id, need to check if bid or succ_id is a loop header
                        if (bid, succ_id) not in edges_not_translated:
                            continue
                        if bid in self.loop_headers:
                            # bid is loop header
                            edges_not_translated.remove((bid, succ_id))  # everything is taken care of, remove
                            continue
                        elif succ_id in self.loop_headers:
                            # unconditional branch into loop (MFSim interprets all loops as do-while)
                            # ensure cgid groups stay together
                            cgid = self.cgid[self.root]
                            if not no_trans and bid not in self.block_transfers:
                                edges_not_translated.remove((bid, succ_id))
                                continue
                            if bid not in self.cgid_pair[self.root].keys():
                                self.cgid_pair[self.root][bid] = self.cgid[self.root]
                            else:
                                check = self.cgid_pair[self.root][bid]
                                if check != self.cgid[self.root]:
                                    cgid = check
                            if self.loop_headers[succ_id]['t'] in self.block_transfers or no_trans:
                                if not no_trans:
                                    out = False
                                    for node in self.block_transfers[bid]:
                                        if node.type == 'out':
                                            out = True
                                    if not out:  # this edge should not be here, remove
                                        edges_not_translated.remove((bid, succ_id))
                                        self.cgid_pair[self.root].pop(bid)
                                        self.cgid[self.root] += 1
                                        continue
                                    if (bid, self.loop_headers[succ_id]['t']) in seen_pair:  # if already handled, move on
                                        edges_not_translated.remove((bid, succ_id))
                                        self.cgid[self.root] += 1
                                        continue
                                conditional_groups[self.cgid[self.root]] = []
                                conditional_groups[self.cgid[self.root]].append(
                                self.write_cond(self.loop_headers[succ_id]['instr'],
                                                cgid, [bid], 1,
                                                [self.loop_headers[succ_id]['t']],
                                                self.expid, 1))
                                seen_pair.append((bid, self.loop_headers[succ_id]['t']))

                                # if conditional is a while, need a path to the false branch as well
                                if 'w' in str(self.program.functions[self.root]['blocks'][succ_id].label) and \
                                        self.loop_headers[succ_id]['f'] is not None and \
                                        len(self.scope_variable) == 0:
                                    conditional_groups[self.cgid[self.root]].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'],
                                                        cgid, [bid], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1))
                                    seen_pair.append((bid, self.loop_headers[succ_id]['f']))
                                edges_not_translated.remove((bid, succ_id))
                                if edges_not_translated:
                                    if (succ_id, self.loop_headers[succ_id]['t']) in edges_not_translated:  # remove this edge if present
                                        edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['t']))
                                    self.cgid[self.root] += 1
                                else:
                                    continue
                            elif self.loop_headers[succ_id]['t'] is None and bid == next(iter(self.block_transfers)):  # this is here for instances of nested conditionals with non active dags such that 't' path is None
                                early_initialize = False
                                if 'w' in str(self.program.functions[self.root]['blocks'][succ_id].label) and self.loop_headers[succ_id]['f'] is not None:  # if conditonal is also a while, must include path to the false branch
                                    conditional_groups[self.cgid[self.root]] = []
                                    conditional_groups[self.cgid[self.root]].append(
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
                                        while val2 not in self.block_transfers.keys():  # move up to next available dag
                                            val2 = val2 + 1
                                if not early_initialize:
                                    conditional_groups[self.cgid[self.root]] = []
                                conditional_groups[self.cgid[self.root]].append(
                                    self.write_cond(self.loop_headers[succ_id]['instr'],
                                                    cgid, [bid], 1,
                                                    [val2],
                                                    self.expid, 1))
                                seen_pair.append((bid, val2))
                                edges_not_translated.remove((bid, succ_id))
                                if 'w' in str(self.program.functions[self.root]['blocks'][succ_id].label): # if while, needs another edge
                                    val2 = val2 + 1
                                    while val2 not in self.block_transfers.keys():
                                        val2 = val2 + 1
                                    if (bid, val2) not in seen_pair:
                                        conditional_groups[self.cgid[self.root]].append(
                                            self.write_cond(self.loop_headers[succ_id]['instr'],
                                                            cgid, [bid], 1,
                                                            [val2],
                                                            self.expid, 1))
                                        seen_pair.append((bid, val2))
                                self.cgid[self.root] += 1
                            elif self.loop_headers[succ_id]['t'] is None:  # case of non active dag, not from the first block transfer
                                val2 = succ_id
                                if len(self.block_transfers.keys()) >= 1:
                                    if succ_id not in self.block_transfers.keys():
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys():
                                            val2 = val2 + 1
                                last = True
                                for l in self.block_transfers[val2]:
                                    if l.type == 'out':
                                        last = False
                                if last:  # if last transfer, skip
                                    edges_not_translated.remove((bid, succ_id))
                                    self.cgid[self.root] += 1
                                    break
                                conditional_groups[self.cgid[self.root]] = []
                                conditional_groups[self.cgid[self.root]].append(
                                    self.write_cond(self.loop_headers[succ_id]['instr'],
                                                    cgid, [bid], 1,
                                                    [val2],
                                                    self.expid, 1))
                                seen_pair.append((bid, val2))
                                edges_not_translated.remove((bid, succ_id))
                                self.cgid[self.root] += 1
                                if edges_not_translated:  # remove edges direcly related to this edge
                                    edges = edges_not_translated
                                    edges_to_remove = list()
                                    for e in edges:
                                        if (e[0] == succ_id or e[1] == succ_id) and e[0] < e[1]:  # retain back edges
                                            edges_to_remove.append(e)
                                    for e in edges_to_remove:
                                        edges_not_translated.remove(e)
                                else:
                                    continue
                            else:  # otherwise the t path is not none, it's simply not in block transfers, need to find transfers manually
                                transfers = list()
                                for inst in edges_not_translated:
                                    if inst[0] == self.loop_headers[succ_id]['t']:
                                        transfers.append(inst[1])
                                conditional_groups[self.cgid[self.root]] = []
                                for t in transfers:
                                    if t not in self.block_transfers:
                                        transfers.remove(t)
                                        for inst in edges_not_translated:  # append edges to blocks that are active
                                            if inst[0] == t and inst[1] in self.block_transfers:
                                                transfers.append(inst[1])
                                for t in transfers:  # for each transfer create a condtional group
                                    conditional_groups[self.cgid[self.root]].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'],
                                                        cgid, [bid], 1,
                                                        [t],
                                                        self.expid, 1))
                                    seen_pair.append((bid, t))
                                edges_not_translated.remove((bid, succ_id))
                                if edges_not_translated:
                                    edges_not_translated.remove((succ_id, self.loop_headers[succ_id]['t']))
                                    self.cgid[self.root] += 1
                                else:
                                    continue

                            conditional_groups[self.cgid[self.root]] = []
                            # find all back edges
                            iteration = 0
                            prev_val = -1
                            dup = False
                            back_edges = [x for x in edges_not_translated if x[1] == succ_id and x[0] > x[1]]
                            for be in back_edges:
                                if dup and iteration < 2:  # allocate space for the duplicated instructions
                                    conditional_groups[self.cgid[self.root]] = []
                                iteration += 1
                                val = be[0]
                                if len(self.block_transfers.keys()) >= 1:
                                    if be[0] not in self.block_transfers.keys():
                                        val = val - 1
                                        while val not in self.block_transfers.keys() and val != -1:  # drop down to active dag
                                            val = val - 1
                                if prev_val == val:
                                    val -= 1
                                prev_val = val
                                if val not in self.block_transfers and not no_trans:  # if val still not in block transfers, it's not a live dag and should be skipped in the cfg
                                    conditional_groups.pop(self.cgid[self.root], None)
                                    edges_not_translated.remove((be[0], succ_id))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    break
                                # ensure cgid groups stay together
                                cgid = self.cgid[self.root]
                                if val not in self.cgid_pair[self.root].keys():
                                    self.cgid_pair[self.root][val] = self.cgid[self.root]
                                else:
                                    check = self.cgid_pair[self.root][val]
                                    if check != self.cgid[self.root]:
                                        cgid = check
                                dup = False
                                if be[0] not in self.block_transfers:  # check the need to duplicate the back edge and out edge for a second conditional (else)
                                    times_to_last_block = 0
                                    for e in edges_not_translated:
                                        if e[1] == be[0]:
                                            times_to_last_block += 1
                                    if times_to_last_block == 2 and iteration < 2:
                                        dup = True
                                        back_edges.append(be)
                                if self.loop_headers[succ_id]['t'] in self.block_transfers or no_trans:
                                    conditional_groups[self.cgid[self.root]].append(
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
                                            elif 'w' in str(self.program.functions[self.root]['blocks'][succ_id].label) and self.loop_headers[succ_id]['f'] is None:  # case for while where f path leads to an inactive dag
                                                transfers4 = list()
                                                for inst in edges_not_translated_save:
                                                    if inst[0] == self.loop_headers[succ_id]['t']:
                                                        transfers4.append(inst[1])
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
                                                    conditional_groups[self.cgid[self.root]].append(
                                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                                        [val], 1,
                                                                        [t],
                                                                        self.expid, 1, 'LOOP'))
                                                    seen_pair.append((val, t))
                                            continue

                                    conditional_groups[self.cgid[self.root]].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                    [val], 1,
                                                    [self.loop_headers[succ_id]['f']],
                                                    self.expid, 1, ))
                                    seen_pair.append((val, self.loop_headers[succ_id]['f']))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[1], self.loop_headers[succ_id]['f']))
                                        self.cgid[self.root] += 1
                                elif self.loop_headers[succ_id]['t'] is None and bid == next(iter(self.block_transfers)):  # for instances of nested conditionals with non active dags such that 't' path is None
                                    val2 = succ_id
                                    if len(self.block_transfers.keys()) >= 1:
                                        if succ_id not in self.block_transfers.keys():
                                            val2 = val2 + 1
                                            while val2 not in self.block_transfers.keys() and val2 != 20:
                                                val2 = val2 + 1
                                    conditional_groups[self.cgid[self.root]].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [val2],
                                                        self.expid, 1, ))
                                    seen_pair.append((val, val2))
                                    if 'w' in str(self.program.functions[self.root]['blocks'][val2].label):  # if a while, needs extra edge
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys() and val2 != 20:
                                            val2 = val2 + 1
                                        if (val, val2) not in seen_pair:
                                            conditional_groups[self.cgid[self.root]].append(
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

                                    conditional_groups[self.cgid[self.root]].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1, ))
                                    seen_pair.append((val, self.loop_headers[succ_id]['f']))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[1], self.loop_headers[succ_id]['f']))
                                        self.cgid[self.root] += 1
                                elif self.loop_headers[succ_id]['t'] is None:  # when a certain edge is missing (repeat)
                                    if (val, val2) not in seen_pair:
                                        conditional_groups[self.cgid[self.root]].append(
                                            self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [val2],
                                                        self.expid, 1, ))
                                        seen_pair.append((val, val2))
                                    if 'w' in str(self.program.functions[self.root]['blocks'][val2].label):  # if a while, needs extra edge
                                        val2 = val2 + 1
                                        while val2 not in self.block_transfers.keys() and val2 != 20:
                                            val2 = val2 + 1
                                        if (val, val2) not in seen_pair:
                                            conditional_groups[self.cgid[self.root]].append(
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
                                    self.cgid[self.root] += 1
                                else:  # create conditional groups for the previously found transfers
                                    for t in transfers:
                                        conditional_groups[self.cgid[self.root]].append(
                                            self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [t],
                                                        self.expid, 1, 'LOOP'))
                                        seen_pair.append((val, t))
                                    if len(transfers) == 0:  # if transfers are empty
                                        val3 = self.loop_headers[succ_id]['t']
                                        while val3 not in self.block_transfers.keys() and val3 != -1:
                                            val3 = val3 - 1
                                        if val3 != 0 and (val, val3) not in seen_pair:
                                            conditional_groups[self.cgid[self.root]].append(
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

                                    conditional_groups[self.cgid[self.root]].append(
                                        self.write_cond(self.loop_headers[succ_id]['instr'], cgid,
                                                        [val], 1,
                                                        [self.loop_headers[succ_id]['f']],
                                                        self.expid, 1, ))
                                    seen_pair.append((val, self.loop_headers[succ_id]['f']))
                                    edges_not_translated.remove((be[1], self.loop_headers[succ_id]['f']))
                                    if dup and iteration < 2:
                                        edges_not_translated.append((be[1], self.loop_headers[succ_id]['f']))
                                        self.cgid[self.root] += 1

                            self.cgid[self.root] += 1
                        else:  # this block is an if conditional
                            if cond: # and executable:
                                self.cblock = block
                                for instr in self.program.functions[self.root]['blocks'][bid].instructions:
                                    if instr.op is IRInstruction.CONDITIONAL:
                                        # ensure cgid groups stay together
                                        cgid = self.cgid[self.root]
                                        if bid not in self.cgid_pair[self.root].keys():
                                            self.cgid_pair[self.root][bid] = self.cgid[self.root]
                                        else:
                                            check = self.cgid_pair[self.root][bid]
                                            if check != self.cgid[self.root]:
                                                cgid = check
                                        if cgid == self.cgid[self.root]:
                                            conditional_groups[self.cgid[self.root]] = []
                                        conditional_groups[cgid].append(
                                            self.write_cond(self.cfg[self.root][bid][instr.iid]['instr'],
                                                            cgid, [bid], 1,
                                                            [self.cfg[self.root][bid][instr.iid]['t']],
                                                            self.expid, 1, 'IF'))
                                        seen_pair.append((bid, self.cfg[self.root][bid][instr.iid]['t']))
                                        # hack for function preceding if statement
                                        try:
                                            edges_not_translated.remove((bid, self.cfg[self.root][bid][instr.iid]['t']))
                                        except:
                                            edges_not_translated.remove(([x for x in self.cfg[self.root]['graph'].successors(bid)][0], self.cfg[self.root][bid][instr.iid]['t']))
                                            pass
                                        if self.cfg[self.root][bid][instr.iid]['f'] is not None:
                                            skip = False
                                            if self.cfg[self.root][bid][instr.iid]['f'] not in self.block_transfers:
                                                skip = True
                                            if skip:  # need to manually find transfers
                                                transfers2 = list()
                                                for inst2 in edges_not_translated:
                                                    if inst2[0] == self.cfg[self.root][bid][instr.iid]['f']:
                                                        transfers2.append(inst2[1])
                                                for t in transfers2:
                                                    if t not in self.block_transfers:
                                                        transfers2.remove(t)
                                                        for inst in edges_not_translated:
                                                            if inst[0] == t:
                                                                transfers2.append(inst[1])
                                                for t in transfers2:
                                                    conditional_groups[self.cgid[self.root]].append(
                                                        self.write_cond(None,
                                                                        cgid, [bid], 1,
                                                                        [t],
                                                                        self.expid, 1))
                                                    seen_pair.append((bid, t))
                                                edges_not_translated.remove((bid, self.cfg[self.root][bid][instr.iid]['f']))
                                                self.cgid[self.root] += 1
                                                continue
                                            to_append = self.write_cond(self.cfg[self.root][bid][instr.iid]['instr'],
                                                                cgid, [bid], 1,
                                                                [self.cfg[self.root][bid][instr.iid]['f']],
                                                                self.expid, 1)
                                            if self.cgid[self.root] not in conditional_groups:
                                                conditional_groups[self.cgid[self.root]] = [to_append]
                                            else:
                                                conditional_groups[self.cgid[self.root]].append(to_append)
                                            seen_pair.append((bid, self.cfg[self.root][bid][instr.iid]['f']))
                                            # hack for function preceding if statement
                                            try:
                                                edges_not_translated.remove((bid, self.cfg[self.root][bid][instr.iid]['f']))
                                            except:
                                                edges_not_translated.remove(([x for x in
                                                                              self.cfg[self.root]['graph'].successors(
                                                                                  bid)][0],
                                                                             self.cfg[self.root][bid][instr.iid]['f']))
                                                edges_not_translated.remove((bid, [x for x in
                                                                              self.cfg[self.root]['graph'].successors(
                                                                                  bid)][0]))
                                                pass
                                self.cgid[self.root] += 1
                            else:  # unconditional exit from an if block
                                # check to see if transfers must be manually found
                                skip = True
                                for to in [self.block_transfers[bid]]:
                                    for to2 in to:
                                        if to2.type in ['out', 'param', 'ret']:
                                            skip = False
                                if succ_id not in self.block_transfers:
                                    skip = True
                                if skip:
                                    if bid > succ_id:
                                        cgid = self.cgid[self.root]
                                        if bid not in self.cgid_pair[self.root].keys():
                                            self.cgid_pair[self.root][bid] = self.cgid[self.root]
                                        else:
                                            check = self.cgid_pair[self.root][bid]
                                            if check != self.cgid[self.root]:
                                                cgid = check
                                        self.cblock = block
                                        conditional_groups[self.cgid[self.root]] = []
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
                                            conditional_groups[self.cgid[self.root]].append(
                                                self.write_cond(None,
                                                                cgid, [bid], 1,
                                                                [t],
                                                                self.expid, 1))
                                            seen_pair.append((bid, t))
                                        self.cgid[self.root] += 1
                                        edges_not_translated.remove((bid, succ_id))
                                        continue
                                    else:
                                        self.cgid[self.root] += 1
                                        edges_not_translated.remove((bid, succ_id))
                                        continue
                                # ensure cgid groups stay together
                                cgid = self.cgid[self.root]
                                if bid not in self.cgid_pair[self.root].keys():
                                    self.cgid_pair[self.root][bid] = self.cgid[self.root]
                                else:
                                    check = self.cgid_pair[self.root][bid]
                                    if check != self.cgid[self.root]:
                                        cgid = check
                                self.cblock = block
                                conditional_groups[self.cgid[self.root]] = []
                                conditional_groups[self.cgid[self.root]].append(
                                    self.write_cond(None,
                                                    cgid, [bid], 1,
                                                    [succ_id],
                                                    self.expid, 1))
                                seen_pair.append((bid, succ_id))
                                edges_not_translated.remove((bid, succ_id))
                                self.cgid[self.root] += 1
                else:  # not an active dag, remove edges directly connected to it
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
            if self.program.config.inline:  # inline optimization
                if root in self.program.symbol_table.functions:
                    continue
            self.root = root
            if root == 'main':
                self.output_path = self.config.output + '/' + self.config.input.rsplit('/', 1)[1][:-3]
                exp_name = self.config.input.rsplit('/', 1)[1][:-3]  # get file input name -'.bs'
                self.is_function = False
            else:
                self.output_path = self.config.output + '/' + self.config.input.rsplit('/', 1)[1][:-3] + '/' + root
                os.makedirs(self.output_path, exist_ok=True)
                exp_name = root
                self.is_function = True
            if self.test:
                cfg_file = StringIO()
            else:
                cfg_file = open("%s/%s.cfg" % (self.output_path, exp_name), "w")
            cfg_file.write("NAME(%s.cfg)\n" % exp_name)
            if self.is_function:
                cfg_file.write("FUNC(F)\n")
            cfg_file.write("\n")

            # conditional groups
            cgs = dict()

            for bid, block in sorted(self.program.functions[root]['blocks'].items()):
                self.cblock = block

                if self.program.config.inline:  # Don't need this if not the main function while inlining
                    # redundant, with new inlining method?
                    if bid is not next(iter(self.program.functions['main']['blocks'])):
                        continue

                write = False
                for instr in block.instructions:
                    if instr.op in [IRInstruction.MIX, IRInstruction.DISPENSE, IRInstruction.DISPOSE,
                                    IRInstruction.HEAT, IRInstruction.SPLIT, IRInstruction.DETECT,
                                    IRInstruction.CALL, IRInstruction.RETURN]:
                            # ['MIX', 'DISPENSE', 'DISPOSE', 'HEAT', 'SPLIT', 'DETECT']:
                        write = True
                        break

                if not write:
                    continue

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
                #         each transfer droplet will have a corresponding TRANSFER_OUT/_IN in the appropriate dags,
                #      See create conditional groups function
                #     """

                if block.instructions[0].op == IRInstruction.CALL:
                    cfg_file.write(f"FC(DAG{bid}, {block.instructions[0].name})\n")
                else:
                    cfg_file.write("DAG(DAG%s)\n" % str(bid))

                if self.test:
                    dag_file = StringIO()
                else:
                    dag_file = open("%s/%s_DAG%s.dag" % (self.output_path, exp_name, str(bid)), "w")
                dag_file.write("DagName (DAG%s)\n" % str(bid))

                os.makedirs(self.output_path + '/figs', exist_ok=True)
                self.dot_file = open("%s/%s_DAG%s.dot" % (self.output_path + '/figs', exp_name, str(bid)), "w")
                self.dot_file.write("digraph G {")

                # for all uses without defs, we must transfer in
                already_transferred_in = dict()
                dispenses = set()
                for node in block.instructions:
                    if node.name in ['DISPENSE']:
                        if hasattr(node.defs['var'], 'points_to'):  # make sure to grab the existing name
                            dispenses.add(node.defs['var'].points_to.name)
                        else:
                            dispenses.add(node.defs['var'].name)
                        # dispenses.add(node.defs['var'].points_to.name)
                        if node.defs['size'] >= 2:  # Check if the offset for a use was left unchanged for a dispense with multiple drops
                            to = list(self.cblock.dag._succ[node.defs['var'].name])
                            index = 0
                            for val in to:
                                for instr in self.cblock.instructions:
                                    if instr.name in {'NOP'}:
                                        continue
                                    if instr.defs['name'] == val:
                                        for use in instr.uses:
                                            if use['name'] == node.defs['name']:
                                                if use['offset'] != 0:  # this means the offset is fine as is
                                                    continue
                                                use['offset'] = index
                                                index = index + 1

                for node in block.instructions:
                    if node.name in ['PHI', 'BINARYOP', 'CONDITIONAL', 'DISPENSE', 'MATH']:
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
                        if points_to in dispenses or points_to in already_transferred_in:
                            continue
                        if use.name not in block.defs:
                            already_transferred_in[points_to] = True
                            if self.is_function and bid == self.program.functions[self.root]['entry']:
                                dag_file.write(self.write_transfer(self.tid, points_to, False, True))
                                # tn = TransferNode(self.tid, bid, points_to, 'param')
                            else:
                                dag_file.write(self.write_transfer(self.tid, points_to, False))
                            tn = TransferNode(self.tid, bid, points_to, 'in')
                            dag_file.write(self.write_edge(self.tid, node.iid))
                            block.defs.add(use.name)
                            self.tid += 1
                        if tn is not None:
                            if bid in self.block_transfers:
                                self.block_transfers[bid].add(tn)
                            else:
                                self.block_transfers[bid] = {tn}

                for a, b in self.live_droplets:  # transfer live droplets if necessary
                    if b in dispenses or b in already_transferred_in or b not in self.program.symbol_table.scope_map[self.root].locals:
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
                    elif node.op is IRInstruction.CALL:
                        dag_file.write(self.write_call(node))
                    elif node.op is IRInstruction.RETURN:
                        dag_file.write(self.write_return(node))
                    elif node.op is IRInstruction.PHI or node.op is IRInstruction.CONDITIONAL or node.op is IRInstruction.MATH or node.op is IRInstruction.NOP:
                        continue
                    else:
                        if self.config.debug:
                            self.log.warning("Unrecognized/unsupported instruction type: %s" % node.name)
                            self.scope_variable = node.defs['var'].points_to.name

                    if node.op in [IRInstruction.MIX, IRInstruction.SPLIT, IRInstruction.RETURN, IRInstruction.DISPOSE, IRInstruction.CALL]:

                        live_drops = list(self.live_droplets)
                        for a, b in live_drops:
                            for use in node.uses:
                                if hasattr(use['var'], 'points_to'):
                                    if b == use['var'].points_to.name:
                                        self.live_droplets.remove((a, b))
                                else:
                                    if b == use['var'].name:
                                        self.live_droplets.remove((a, b))
                        if node.op not in [IRInstruction.DISPOSE, IRInstruction.RETURN]:
                            if hasattr(node.defs['var'], 'points_to'):
                                self.live_droplets.append((bid, node.defs['var'].points_to.name))
                            else:
                                self.live_droplets.append((bid, node.defs['var'].name))


                # for all defs without uses, we must transfer out (if used elsewhere)
                #   or dispose (if never used again)

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
                                if hasattr(i.defs['var'], 'points_to'): # make sure to grab the existing name
                                    _def = i.defs['var'].points_to.name
                                else:
                                    _def = i.defs['var'].name
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
                        if i.name == 'PHI':
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
                        tn = None
                        try:
                            reachable = (
                                {x for v in dict(nx.bfs_successors(self.cfg[self.root]['graph'], bid)).values() for x in v})
                        except nx.NetworkXError as e:
                            # self.log.warning("Droplet {} is not being disposed or saved.".format(_def))
                            return trans
                        for s in reachable:
                            if trans:
                                break
                            sblock = self.program.functions[root]['blocks'][s]
                            for si in sblock.instructions:
                                if si.op in {IRInstruction.PHI, IRInstruction.CONDITIONAL, IRInstruction.NOP}:
                                    continue
                                if trans:
                                    break
                                if si.name == 'DISPENSE':
                                    x = si.uses[0]['name']
                                else:
                                    x = [x['var'].points_to.name for x in si.uses if type(x['var']) is not Symbol]
                                if _def in x:
                                    dag_file.write(self.write_edge(instr.iid, self.tid))
                                    dag_file.write(self.write_transfer(self.tid, _def, True))
                                    # need a 'param' transfer, not just a
                                    if sblock.instructions[0].op == IRInstruction.CALL:
                                        # print("ok")
                                        tn = TransferNode(self.tid, bid, _def, 'param')
                                    elif instr.op == IRInstruction.CALL:
                                        tn = TransferNode(self.tid, bid, _def, 'ret')
                                    else:
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

                    if not transferred and points_to in [x[1] for x in self.live_droplets]:  # what to do with this droplet?
                        if self.config.debug and not self.test:
                            self.log.warning(
                                "No more operations for {}, warning will appear in {}".format(_def, dag_file.name))
                        dag_file.write("// **NO MORE OPERATIONS FOR {}; SHOULD SAVE OR DISPOSE**".format(_def))
                    if tn is not None:
                        if bid in self.block_transfers:
                            self.block_transfers[bid].add(tn)
                        else:
                            self.block_transfers[bid] = {tn}

                if not self.test:
                    dag_file.close()
                self.num_dags += 1
                self.dot_file.write("\n}")
                self.dot_file.close()
                os.system("dot -Tpng {}/{}_DAG{}.dot -o {}/{}_DAG{}.png".format(self.output_path + '/figs', exp_name, str(bid),
                                                                                self.output_path + '/figs', exp_name, str(bid)))

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
            # see create_conditional_groups function

            edges_not_translated = list(nx.edges(self.cfg[self.root]['graph']))

            conditional_groups = self.create_conditional_groups(edges_not_translated)

            self.num_cgs = len(self.cgid_pair[self.root])
            cfg_file.write("\nNUMCGS(%s)\n\n" % self.num_cgs)

            for cg in conditional_groups.values():
                for val in cg:
                    cfg_file.write(val)

            if not self.test:
                cfg_file.close()

        return True

    def write_branch(self) -> str:
        pass

    def write_expression(self) -> str:
        pass
