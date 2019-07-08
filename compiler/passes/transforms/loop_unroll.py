from compiler.data_structures import *
from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform
import networkx as nx
import copy



class LoopUnroll(BSTransform):

    def __init__(self):
        super().__init__("LoopUnravel")
        self.log.warn("Starting Loop Unrolling.....")

    def loop_condition(self, RO, x, y):
        if RO == RelationalOps.EQUALITY:
            return True if x == y else False
        elif RO == RelationalOps.NE:
            return True if x != y else False
        elif RO == RelationalOps.LT:
            return True if x < y else False
        elif RO == RelationalOps.LTE:
            return True if x <= y else False
        elif RO == RelationalOps.GT:
            return True if x > y else False
        elif RO == RelationalOps.GTE:
            return True if x >= y else False
        else:
            return False

    def reevaluate(self, BO: BinaryOp, x, y):
        if BO.op == BinaryOps.SUBTRACT:
            x = x - y
        elif BO.op == BinaryOps.ADD:
            x = x + y
        elif BO.op == BinaryOps.MULTIPLE:
            x = x * y
        elif BO.op == BinaryOps.DIVIDE:
            x = x / y
        elif BO.op == BinaryOps.AND:
            x = x & y
        elif BO.op == BinaryOps.OR:
            x = x | y
        return x

    def finite_loop(self, bin_op, x, y, z, inductive_step=True):
        k = self.reevaluate(bin_op, x, y)
        k_delta = k - z
        zx_delta = x - z
        zk_delta = abs(zx_delta) - abs(k_delta)
        if inductive_step: i_step = self.finite_loop(bin_op, k, y, z, False)
        else: i_step = True

        return True if zk_delta > 0 and i_step else False

    def unroll(self, program: Program) -> Program:
        global jump
        for root in program.functions:

            tlist = []
            node_one = list(nx.nodes(program.functions[root]['graph']))
            dominators = (nx.immediate_dominators(program.functions[root]['graph'],1))
            sorted_doms = sorted(dominators.items())
            for item in dominators:
                edge_list = list(program.functions[root]['graph'].out_edges(item))
                if len(edge_list) > 0:
                    for edge in edge_list:
                        if edge in sorted_doms:
                            tlist.append(edge)

            for item in tlist:
                if len(item) > 2:
                    continue
                child = item[0]
                parent = item[1]

                pure_child_ins = copy.deepcopy(program.functions[root]['blocks'][child].instructions)
                pure_parent_ins = copy.deepcopy(program.functions[root]['blocks'][parent].instructions)
                c_label = program.functions[root]['blocks'][child].label

                label = None
                binary_operation = None
                jump = None
                labels = []
                # IDENTIFY - rewrite to implement dominator algorithm
                nested_multiplier = 0
                # Parent Instructions
                l_left = l_right = None
                for p_instructions in program.functions[root]['blocks'][parent].instructions:
                    if type(p_instructions) == Conditional:
                        if c_label.label == p_instructions.true_branch.label:
                            label = program.functions[root]['blocks'][parent].instructions.pop(
                                program.functions[root]['blocks'][parent].instructions.index(p_instructions))
                            nested_multiplier +=1
                            labels.append(label)
                            l_left = label.left

                            l_right = label.right

                    else:
                        pass
                bad_loop = True
                # Child Instructions
                # TODO: Fix Child end Jump Detection
                if program.functions[root]['blocks'][child].instructions[-1] == Jump:
                    jump = program.functions[root]['blocks'][child].instructions.pop(-1)
                else:
                    jump = None
                for c_instructions in program.functions[root]['blocks'][child].instructions:
                    if type(c_instructions) == BinaryOp:
                        binary_operation = c_instructions
                        if l_left != None and binary_operation.defs.name[:-1] == l_left.name:
                            program.functions[root]['blocks'][child].instructions.pop(program.functions[root]['blocks'][child].instructions.index(c_instructions))
                            bad_loop = False
                        elif l_right != None and binary_operation.defs.name[:-1] == l_right.name:
                            program.functions[root]['blocks'][child].instructions.pop(program.functions[root]['blocks'][child].instructions.index(c_instructions))
                            bad_loop = False
                    else:
                        pass
                if label is None or binary_operation is None:
                    bad_loop = True

                # EXECUTE
                # Warning 0: This Code Works as
                # IDENTyOp Chec
                # 4 Cases:suming the right is the constant
                # Warning 1: This Code is not fully functional: it cannot find the original x value
                is_finite = False
                if bad_loop is False:
                    constant = 1
                    # Can't get current variable value, assume 1 because we already have 1 "set"
                    # of instructions
                    base_instructions_unf = program.functions[root]['blocks'][child].instructions.copy()
                    base_instructions = list(filter(lambda i : not(type(i) is Jump), base_instructions_unf))
                    program.functions[root]['blocks'][child].instructions = base_instructions.copy()
                    is_finite = self.finite_loop(binary_operation, constant, int(binary_operation.right),
                                             label.right.value)
                if is_finite:
                    while self.loop_condition(label.relop.value, constant, label.right.value*nested_multiplier):
                        program.functions[root]['blocks'][child].instructions +=base_instructions
                        constant = self.reevaluate(binary_operation, constant, int(binary_operation.right))
                    # CLEANUP: Pops Parent, adds jump, redoes the labels.
                    if jump is not None:
                        jump.jumps = label.false_branch
                        program.functions[root]['blocks'][child].instructions.extend(jump)

                    jumpy = Jump(label.true_branch)
                    program.functions[root]['blocks'][parent].instructions.append(jumpy)
                    program.functions[root]['blocks'][child].label = label.true_branch

                    program.functions[root]['blocks'][child].jumps.pop()
                    program.functions[root]['blocks'][child].instructions.append(Jump(program.functions[root]['blocks'][child+1].label))
                else:
                    bad_loop = True

                if bad_loop:
                    program.functions[root]['blocks'][parent].instructions = pure_parent_ins
                    program.functions[root]['blocks'][child].instructions = pure_child_ins
                    self.log.warn("Found Unrollable Loop... resetting instructions..")
        for root in program.functions:
            for block in program.functions[root]['blocks']:
                self.log.warn(program.functions[root]['blocks'][block])
        self.log.warn("Loop Unrolling Completed")
        # Test code showing program post unroll
        return program

    # Entry Point
    def transform(self, program: Program) -> Program:
        for root in program.functions:
            for block in program.functions[root]['blocks']:
                self.log.warn(program.functions[root]['blocks'][block])
        self.log.warn("Loop Unrolling Completed")
        # Test Print to show pre-unroll
        # Test function
        return self.unroll(program)
