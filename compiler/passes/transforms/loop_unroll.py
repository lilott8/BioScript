from compiler.data_structures import *
from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform
import networkx as nx


class LoopUnroll(BSTransform):

    def __init__(self):
        super().__init__("LoopUnravel")
        self.log.warn("Starting Loop Unrolling.....")

    def getCondition(self, RO, x, y):
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

    def calculateNewValue(self, BO: BinaryOp, x, y):
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

    # TODO: Use "Induction" to determine finite loops
    def inductionProof(self, BO, RO, x, y):
        return False

    def unroll(self, program: Program) -> Program:
        global jump
        for root in program.functions:
            tlist = list(nx.simple_cycles(program.functions[root]['graph']))
            for item in tlist:
                child = item[1]
                parent = item[0]
                label = None
                binary_operation = None
                jump = None
                labels = []
                # IDENTIFY
                # TODO: Better Identification of Conditionals
                # Parent Instructions
                for p_instructions in program.functions[root]['blocks'][parent].instructions:
                    if type(p_instructions) == Conditional:
                        self.log.warn("Success")
                        label = program.functions[root]['blocks'][parent].instructions.pop(
                            program.functions[root]['blocks'][parent].instructions.index(p_instructions))
                        labels.append(label)
                        l_left = label.left
                        l_right = label.right
                    else:
                        pass
                # Child Instructions
                jump = program.functions[root]['blocks'][child].instructions.pop(-1)
                badloop = True
                for c_instructions in program.functions[root]['blocks'][child].instructions:
                    if type(c_instructions) == BinaryOp:
                        self.log.warn("Success")
                        # TODO:  Better BinaryOp Chec
                        # 4 Cases:
                        binary_operation = program.functions[root]['blocks'][child].instructions.pop(
                            program.functions[root]['blocks'][child].instructions.index(c_instructions))
                        if binary_operation.defs.name[:-1] == l_left.name:
                            badloop = False
                        elif binary_operation.defs.name[:-1] == l_right.name:
                            badloop = False
                    else:
                        pass
                if jump is None or label is None or binary_operation is None or badloop:
                    self.log.warn("Bad or Infinite Loop Detected... aborting unroll")
                    continue
                # EXECUTE
                constant = 1
                base_instructions = program.functions[root]['blocks'][child].instructions.copy()
                while self.getCondition(label.relop.value, constant, label.right.value):
                    program.functions[root]['blocks'][child].instructions.extend(base_instructions)
                    constant = self.calculateNewValue(binary_operation, constant, int(binary_operation.right))
                # CLEANUP: Pops Parent, adds jump, redoes the labels.
                jump.jumps = label.false_branch
                program.functions[root]['blocks'][child].instructions.append(jump)
                program.functions[root]['blocks'].pop(parent)
                program.functions[root]['blocks'][child].label = label.true_branch
                program.functions[root]['blocks'][child].jumps.pop()

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
