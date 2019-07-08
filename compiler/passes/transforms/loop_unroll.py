from compiler.data_structures import *
from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform
import networkx as nx
import copy



class LoopUnroll(BSTransform):

    def __init__(self):
        super().__init__("LoopUnravel")
        self.log.warn("Starting Loop Unrolling.....")

    def loop_condition(self, RelOp, left, right):
        if RelOp == RelationalOps.EQUALITY:
            return True if left == right else False
        elif RelOp == RelationalOps.NE:
            return True if left != right else False
        elif RelOp == RelationalOps.LT:
            return True if left < right else False
        elif RelOp == RelationalOps.LTE:
            return True if left <= right else False
        elif RelOp == RelationalOps.GT:
            return True if left > right else False
        elif RelOp == RelationalOps.GTE:
            return True if left >= right else False
        else:
            return False

    def reevaluate(self, BinOp: BinaryOp, left, right):
        if BinOp.op == BinaryOps.SUBTRACT:
            left = left - right
        elif BinOp.op == BinaryOps.ADD:
            left = left + right
        elif BinOp.op == BinaryOps.MULTIPLE:
            left = left * right
        elif BinOp.op == BinaryOps.DIVIDE:
            left = left / right
        elif BinOp.op == BinaryOps.AND:
            left = left & right
        elif BinOp.op == BinaryOps.OR:
            left = left | right
        return left

    def finite_loop(self, bin_op, left: int, modifier: int, right: int, inductive_step=True):
        left_modified = self.reevaluate(bin_op, left, modifier)
        left_modified_right_delta = left_modified - right
        left_right_delta = left - right
        lmrd_lrd_delta = left_right_delta - left_modified_right_delta
        if inductive_step: i_step = self.finite_loop(bin_op, left_modified, modifier, right, False)
        else: i_step = True

        return True if abs(lmrd_lrd_delta) > 0 and i_step else False

    def unroll(self, program: Program) -> Program:
        global jump_from_loop_body
        for root in program.functions:

            loop_list = []
            dominators = (nx.immediate_dominators(program.functions[root]['graph'],1))
            sorted_doms = sorted(dominators.items())
            for loop in dominators:
                edge_list = list(program.functions[root]['graph'].out_edges(loop))
                if len(edge_list) > 0:
                    for edge in edge_list:
                        if edge in sorted_doms:
                            loop_list.append(edge)

            for loop in loop_list:
                if len(loop) > 2:
                    continue
                loop_body = loop[0]
                head = loop[1]

                pure_child_ins = copy.deepcopy(program.functions[root]['blocks'][loop_body].instructions)
                pure_parent_ins = copy.deepcopy(program.functions[root]['blocks'][head].instructions)
                c_label = program.functions[root]['blocks'][loop_body].label

                label = None
                binary_operation = None
                jump_from_loop_body = None
                labels = []
                # IDENTIFY
                nested_multiplier = 0
                # Head Instructions
                l_left = l_right = None
                for p_instructions in program.functions[root]['blocks'][head].instructions:
                    if type(p_instructions) == Conditional:
                        if c_label.label == p_instructions.true_branch.label:
                            label = program.functions[root]['blocks'][head].instructions.pop(
                                program.functions[root]['blocks'][head].instructions.index(p_instructions))
                            nested_multiplier +=1
                            labels.append(label)
                            l_left = label.left

                            l_right = label.right

                    else:
                        pass
                bad_loop = True

                if program.functions[root]['blocks'][loop_body].instructions[-1] == Jump:
                    jump_from_loop_body = program.functions[root]['blocks'][loop_body].instructions.pop(-1)
                else:
                    jump_from_loop_body = None
                for c_instructions in program.functions[root]['blocks'][loop_body].instructions:
                    if type(c_instructions) == BinaryOp:
                        binary_operation = c_instructions
                        if l_left != None and binary_operation.defs.name[:-1] == l_left.name:
                            program.functions[root]['blocks'][loop_body].instructions.pop(program.functions[root]['blocks'][loop_body].instructions.index(c_instructions))
                            bad_loop = False
                        elif l_right != None and binary_operation.defs.name[:-1] == l_right.name:
                            program.functions[root]['blocks'][loop_body].instructions.pop(program.functions[root]['blocks'][loop_body].instructions.index(c_instructions))
                            bad_loop = False
                    else:
                        pass
                if label is None or binary_operation is None:
                    bad_loop = True

                # EXECUTE
                # TODO: Refactor when Numbers are fixed
                is_finite = False
                if bad_loop is False:
                    constant = 1

                    base_instructions_unf = program.functions[root]['blocks'][loop_body].instructions.copy()
                    base_instructions = list(filter(lambda i : not(type(i) is Jump), base_instructions_unf))
                    program.functions[root]['blocks'][loop_body].instructions = base_instructions.copy()
                    is_finite = self.finite_loop(binary_operation, constant, int(binary_operation.right),
                                             label.right.value)
                if is_finite:
                    while self.loop_condition(label.relop.value, constant, label.right.value*nested_multiplier):
                        program.functions[root]['blocks'][loop_body].instructions +=base_instructions
                        constant = self.reevaluate(binary_operation, constant, int(binary_operation.right))
                    # CLEANUP: Adds the correct jump paths
                    if jump_from_loop_body is not None:
                        jump_from_loop_body.jumps = label.false_branch
                        program.functions[root]['blocks'][loop_body].instructions.extend(jump_from_loop_body)

                    jump_from_head = Jump(label.true_branch)
                    program.functions[root]['blocks'][head].instructions.append(jump_from_head)
                    program.functions[root]['blocks'][loop_body].label = label.true_branch

                    program.functions[root]['blocks'][loop_body].jumps.pop()
                    program.functions[root]['blocks'][loop_body].instructions.append(Jump(program.functions[root]['blocks'][loop_body+1].label))
                else:
                    bad_loop = True

                if bad_loop:
                    program.functions[root]['blocks'][head].instructions = pure_parent_ins
                    program.functions[root]['blocks'][loop_body].instructions = pure_child_ins
                    self.log.warn("Found Unrollable Loop... resetting instructions..")
        # for root in program.functions:
        #     for block in program.functions[root]['blocks']:
        #         self.log.warn(program.functions[root]['blocks'][block])
        # self.log.warn("Loop Unrolling Completed")
        return program

    # Entry Point
    def transform(self, program: Program) -> Program:
        # for root in program.functions:
        #     for block in program.functions[root]['blocks']:
        #         self.log.warn(program.functions[root]['blocks'][block])
        # self.log.warn("Loop Unrolling Completed")
        return self.unroll(program)
