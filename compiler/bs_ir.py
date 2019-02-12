from shared.enums.instructions import *


class IR(object):

    def __init__(self, op: Instruction):
        self.op = op
        self.name = op.name
        self.uses = set()
        self.defs = set()
        # Does this operation consume uses.
        self.consumes = False
        # Does this need to insert extra instructions?
        self.is_simd = False


class ControlIR(IR):

    def __init__(self, op: Instruction):
        super().__init__(op)
        self.condition = ""
        # first is true, last is else
        self.jumps = list()


class HeatIR(IR):

    def __init__(self):
        super().__init__(Instruction.HEAT)


class MixIR(IR):

    def __init__(self):
        super().__init__(Instruction.MIX)
        self.consumes = True


class DispenseIR(IR):

    def __init__(self):
        super().__init__(Instruction.DISPENSE)


class DisposeIR(IR):

    def __init__(self):
        super().__init__(Instruction.DISPOSE)
        self.consumes = True


class SplitIR(IR):

    def __init__(self):
        super().__init__(Instruction.SPLIT)
        self.consumes = True


class DetectIR(IR):

    def __init__(self):
        super().__init__(Instruction.DETECT)


class LoopIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.LOOP)


class BranchIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.BRANCH)


class MethodIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.METHOD)
        # List of args passed to function.
        self.args = list()
