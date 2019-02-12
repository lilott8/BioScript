import colorlog

from shared.enums.instructions import *


class IR(object):

    def __init__(self, op: Instruction):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.op = op
        self.name = op.name
        self.uses = set()
        self.defs = set()
        # Does this operation consume uses.
        self.consumes = False
        # Does this need to insert extra instructions?
        self.is_simd = False

    def __repr__(self):
        output = "{}: \t".format(self.name)

        output += "Defs: {"
        defs = ""
        for d in self.defs:
            defs += "{}, ".format(d.name)
        if defs:
            defs = defs[:-2]
        output += defs + "}\t"

        output += "Uses: {"
        uses = ""
        for u in self.uses:
            uses += "{}, ".format(u.name)
        if uses:
            uses = uses[:-2]
        output += uses + "}\n"

        return output


class ControlIR(IR):

    def __init__(self, op: Instruction):
        super().__init__(op)
        self.condition = ""
        # first is true, last is else
        self.jumps = list()

    def __repr__(self):
        output = super().__repr__()
        output += "\t Condition: {}\n".format(self.condition)
        return output


class HeatIR(IR):

    def __init__(self):
        super().__init__(Instruction.HEAT)

    def __repr__(self):
        return super().__repr__()

    def __str__(self):
        return self.__repr__()


class MixIR(IR):

    def __init__(self):
        super().__init__(Instruction.MIX)
        self.consumes = True

    def __repr__(self):
        return super().__repr__()

    def __str__(self):
        return self.__repr__()


class DispenseIR(IR):

    def __init__(self):
        super().__init__(Instruction.DISPENSE)
        self.consumes = False

    def __repr__(self):
        return super().__repr__()


class DisposeIR(IR):

    def __init__(self):
        super().__init__(Instruction.DISPOSE)
        self.consumes = True

    def __repr__(self):
        return super().__repr__()


class SplitIR(IR):

    def __init__(self):
        super().__init__(Instruction.SPLIT)
        self.consumes = True

    def __repr__(self):
        return super().__repr__()


class DetectIR(IR):

    def __init__(self):
        super().__init__(Instruction.DETECT)

    def __repr__(self):
        return super().__repr__()


class NumericIR(IR):

    def __init__(self):
        super().__init__(Instruction.EXPRESSION)
        self.expression = ""

    def __repr__(self):
        output = super().__repr__()
        return output + self.expression + "\n"


class LoopIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.LOOP)

    def __repr__(self):
        return super().__repr__()


class BranchIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.BRANCH)

    def __repr__(self):
        return super().__repr__()


class MethodIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.METHOD)
        # List of args passed to function.
        self.args = list()

    def __repr__(self):
        return super().__repr__()


class ReturnIR(ControlIR):

    def __init__(self):
        super().__init__(Instruction.RETURN)
        self.return_var = None

    def __repr__(self):
        output = super().__repr__()
        output += self.return_var
        return output + "\n"
