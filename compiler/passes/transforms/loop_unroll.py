from compiler.data_structures import *
from compiler.data_structures.program import Program
from compiler.passes.transforms.bs_transform import BSTransform
import networkx as nx


class LoopUnroll(BSTransform):

    def __init__(self):
        super().__init__("LoopUnravel")
        self.log.warn("Starting Loop Unrolling.....")

    def unroll(self, program: Program) -> Program:
        global jump
        for root in program.functions:
                #try:
                    glist = list(nx.find_cycle(program.functions[root]['graph']))
                    tlist = list(nx.simple_cycles(program.functions[root]['graph']))
                    for item in tlist:
                        child = item[1]
                        parent = item[0]
                        self.log.warn(child)
                        label = None
                        BO = None
                        jump = None

                        # remove end char from each item in set.
                        # compare to binaryOp item
                        variables = program.functions[root]['blocks'][parent].uses
                        labels = []


                        #check to se

                        self.log.warn(variables)
                        for items in program.functions[root]['blocks'][parent].instructions:
                            if type(items) == Conditional:
                                self.log.warn("Success")
                                label = program.functions[root]['blocks'][parent].instructions.pop(
                                    program.functions[root]['blocks'][parent].instructions.index(items))
                                labels.append(label)
                                l_left = label.left
                                l_right = label.right
                            else:
                                pass
                        # Remove Jumps
                        self.log.warn(labels)
                        # CHILD MODIFICATIONS
                        jump = program.functions[root]['blocks'][child].instructions.pop(-1)
                        BadLoop = True
                        for items2 in program.functions[root]['blocks'][child].instructions:

                            if type(items2) == BinaryOp:
                                self.log.warn("Success")
                                # TODO:  Better BinaryOp Chec
                                # 4 Cases:
                                BO = program.functions[root]['blocks'][child].instructions.pop(
                                    program.functions[root]['blocks'][child].instructions.index(items2))
                                if BO.defs.name[:-1] == l_left.name:
                                    BadLoop = False
                                elif  BO.defs.name[:-1] == l_right.name:
                                    BadLoop = False

                            else:
                                pass
                        #	self.log.warn(jump + "Henlo" )
                        if jump is None or label is None or BO is None or BadLoop:
                            self.log.warn(BadLoop)
                            self.log.warn("Bad or Infinite Loop Detected... aborting unroll")
                            continue

                        keep_looping = True
                        # check variable in l_left or l_right is in bo_defs
                        # EXECUTE
                        if BinaryOps.SUBTRACT == BO.op:
                            constant = 8
                            base_instructions = program.functions[root]['blocks'][child].instructions.copy()
                            while constant > 1:
                                program.functions[root]['blocks'][child].instructions.extend(base_instructions)
                                constant -= 1
                        elif BinaryOps.ADD == BO.op:
                            constant = 1
                            base_instructions = program.functions[root]['blocks'][child].instructions.copy()


                            while keep_looping:
                                if label.relop.value == 4:

                                    if  constant < label.right.value:
                                        program.functions[root]['blocks'][child].instructions.extend(base_instructions)
                                        constant += int(BO.right)
                                    else:
                                        keep_looping = False
                                elif label.relop.value == 0:
                                    if  constant == label.right.value:
                                        program.functions[root]['blocks'][child].instructions.extend(base_instructions)
                                        constant += int(BO.right)
                                    else:
                                        keep_looping = False
                                else:
                                    keep_looping = False
                        elif BinaryOps.MULTIPLE == BO.op:
                            constant = 1
                            base_instructions = program.functions[root]['blocks'][child].instructions.copy()

                            while keep_looping:
                                if label.relop.value == 4:

                                    if constant < label.right.value :
                                        program.functions[root]['blocks'][child].instructions.extend(base_instructions)
                                        constant *= int(BO.right)
                                    else:
                                        keep_looping = False
                                elif label.relop.value == 0:
                                    if constant == label.right.value:
                                        program.functions[root]['blocks'][child].instructions.extend(base_instructions)
                                        constant *= int(BO.right)
                                    else:
                                        keep_looping = False
                                else:
                                    keep_looping = False
                            pass
                        elif BinaryOps.DIVIDE == BO.op:
                            pass
                        else:
                            pass

                        # CLEANUP: Pops Parent, adds jump, redoes the labels.
                        jump.jumps = label.false_branch
                        program.functions[root]['blocks'][child].instructions.append(jump)
                        program.functions[root]['blocks'].pop(parent)
                        program.functions[root]['blocks'][child].label = label.true_branch
                        program.functions[root]['blocks'][child].jumps.pop()

                #except:
                        self.log.warn("No Loops Found in Function")
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
