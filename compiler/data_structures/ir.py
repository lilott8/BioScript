from compiler.data_structures.function import Function
from compiler.data_structures.registers import *


class IRInstruction(IntEnum):
    # Expressions
    CONSTANT = 0
    TEMP = 1
    BINARYOP = 2
    CALL = 3
    NAME = 4
    # Statements
    MIX = 5
    SPLIT = 6
    DETECT = 7
    HEAT = 8
    DISPENSE = 9
    DISPOSE = 10
    STORE = 11
    # Control
    JUMP = 12
    CONDITIONAL = 13
    LABEL = 14
    RETURN = 15
    # Meta
    USEBY = 16
    EXECUTEFOR = 17
    NOP = 18
    PHI = 19


class BinaryOps(IntEnum):
    ADD = 0
    SUBTRACT = 1
    MULTIPLE = 2
    DIVIDE = 3
    OR = 4
    AND = 5


class RelationalOps(IntEnum):
    EQUALITY = 0
    NE = 1
    LT = 2
    LTE = 3
    GT = 4
    GTE = 5

    def get_readable(self):
        if self.value == RelationalOps.EQUALITY:
            return "=="
        if self.value == RelationalOps.NE:
            return "!="
        if self.value == RelationalOps.LT:
            return "<"
        if self.value == RelationalOps.LTE:
            return "<="
        if self.value == RelationalOps.GT:
            return ">"
        else:
            return ">="


class InstructionSet(object):
    instructions = {IRInstruction.MIX, IRInstruction.SPLIT, IRInstruction.DETECT, IRInstruction.DISPENSE,
                    IRInstruction.DISPOSE, IRInstruction.HEAT, IRInstruction.CALL, IRInstruction.BINARYOP}

    BinaryOps = {BinaryOps.AND, BinaryOps.ADD, BinaryOps.DIVIDE, BinaryOps.MULTIPLE, BinaryOps.OR, BinaryOps.SUBTRACT}


class IR(object):

    def __init__(self, op: IRInstruction):
        self.op = op
        self.name = op.name

    def __repr__(self):
        return self.name

    def __str__(self):
        return self.name


class NOP(IR):
    def __init__(self):
        super().__init__(IRInstruction.NOP)


"""
========================================================
Expression IR:
    Deals with computation of some value
========================================================
"""


class Expression(IR):
    def __init__(self, op: IRInstruction):
        super().__init__(op)


class Constant(Expression):
    def __init__(self, value: float):
        super().__init__(IRInstruction.CONSTANT)
        self.value = value

    def __str__(self):
        return "CONSTANT: {}".format(self.value)

    def __repr__(self):
        return self.__str__()


class Temp(Expression):
    def __init__(self, value: Variable):
        super().__init__(IRInstruction.TEMP)
        self.value = value

    def __str__(self):
        return "TEMP: {}".format(self.value)

    def __repr__(self):
        return self.__str__()


class BinaryOp(Expression):
    def __init__(self, left: Expression, right: Expression, op: BinaryOps):
        super().__init__(IRInstruction.BINARYOP)
        self.left = left
        self.right = right
        self.op = op

    def __str__(self):
        return "BINARYOP {} {} {}".format(self.op, self.left, self.right)


class Call(Expression):
    def __init__(self, func: Function):
        super().__init__(IRInstruction.CALL)
        self.function = func
        self.args = self.function.args
        self.name = self.function.name
        self.uses = func.args


class Name(Expression):
    def __init__(self, name: str):
        super().__init__(IRInstruction.NAME)
        self.name = name


"""
========================================================
Statement IR:
    Operations that move the program from one state
    to another.  This includes instructions that
    can mutate the store.
========================================================
"""


class Statement(IR):
    def __init__(self, op: IRInstruction, out, execute_for=(-1, BSTime.SECOND), use_by=None):
        super().__init__(op)
        self.uses = []
        self.defs = out
        self.execute_for = ExecuteFor(execute_for[0], execute_for[1])
        self.use_by = None
        if use_by:
            self.use_by = UseBy(use_by[0], use_by[1])

    def __str__(self):
        return "{}: out-register: {}, in-values: [{}]".format(super().__str__(), self.defs, self.uses)


class Mix(Statement):
    def __init__(self, out: Temp, one: Temp, two: Temp,
                 execute_for: (float, BSTime) = (10, BSTime.SECOND), use_by: (float, BSTime) = None):
        super().__init__(IRInstruction.MIX, out, execute_for, use_by)
        self.uses.extend([one, two])

    def __str__(self):
        return "{} = mix({}, {})".format(self.defs, self.uses[0], self.uses[1])


class Split(Statement):
    def __init__(self, out: Temp, one: Temp, size: int, execute_for: (float, BSTime) = (-1, BSTime.SECOND),
                 use_by: (float, BSTime) = None):
        super().__init__(IRInstruction.SPLIT, out, execute_for, use_by=use_by)
        self.uses.append(one)
        self.size = size


class Detect(Statement):
    def __init__(self, module: Temp, out: Temp, execute_for: (float, BSTime)):
        super().__init__(IRInstruction.DETECT, out, execute_for)
        self.module = module


class Heat(Statement):
    def __init__(self, out: Temp, reagent: Temp, execute_for: (float, BSTime),
                 use_by: (float, BSTime) = None, heat_for: (float, BSTime) = (10, BSTime.SECOND)):
        super().__init__(IRInstruction.HEAT, out, execute_for, use_by=use_by)
        self.uses.append(reagent)
        self.time = heat_for


class Dispense(Statement):
    def __init__(self, out: Temp, reagent: Temp):
        super().__init__(IRInstruction.DISPENSE, out)
        self.uses.append(reagent)


class Dispose(Statement):
    def __init__(self, out: Output, reagent: Temp):
        super().__init__(IRInstruction.DISPOSE, out)
        self.uses.append(reagent)


class Store(Statement):
    def __init__(self, out: Temp, value: Expression):
        super().__init__(IRInstruction.STORE, out)
        self.uses.append(value)

    def __str__(self):
        return "{} = {}".format(self.defs, self.uses)


"""
========================================================
Control IR:
    Operations that can move control of the program
    from one place to another.
========================================================
"""


class Control(IR):
    def __init__(self, op: IRInstruction):
        super().__init__(op)


class Label(Control):

    def __init__(self, name: str):
        super().__init__(IRInstruction.LABEL)
        self.label = name

    def __str__(self):
        return "LABEL: " + self.label

    def __repr__(self):
        return self.__str__()


class Jump(Control):

    def __init__(self, jump_to: Label):
        super().__init__(IRInstruction.JUMP)
        # first is true, last is else
        self.jumps = jump_to

    def __str__(self):
        return "JUMP {}".format(self.jumps)


class Conditional(Control):

    def __init__(self, relop: RelationalOps, left: Expression, right: Expression,
                 t_branch: Label = None, f_branch: Label = None):
        super().__init__(IRInstruction.CONDITIONAL)
        # first is true, last is else
        self.true_branch = t_branch
        self.false_branch = f_branch
        self.relop = relop
        self.left = left
        self.right = right
        self.uses = [right, left]
        self.defs = None

    def __str__(self):
        return "({} {} {}) T: {}\tF:{}".format(self.left, self.relop.get_readable(), self.right, self.true_branch,
                                               self.false_branch)

    def __repr__(self):
        return self.__str__()


class Return(Control):

    def __init__(self, return_value: Expression, return_to: Label):
        super().__init__(IRInstruction.RETURN)
        self.return_value = return_value
        self.return_to = return_value


"""
========================================================
Meta IR:
    Instructions that can, in certain cases be ignored,
    but are essential in timing annotations or 
    instruction constraints in the form of waiting
========================================================
"""


class Meta(IR):

    def __init__(self, op: IRInstruction):
        super().__init__(op)


class Phi(Meta):
    def __init__(self, left: Expression, right: list):
        super().__init__(IRInstruction.PHI)
        self.defs = left
        self.uses = right

    def __str__(self):
        out = "{} = Phi(".format(self.defs)
        temp = ""
        for r in self.uses:
            temp += "{}, ".format(r)
        temp = temp[:-2]
        out += temp + ")"
        return out


class TimeConstraint(Meta):
    def __init__(self, op: IRInstruction, time: float = 10, unit: BSTime = BSTime.SECOND):
        super().__init__(op)
        self.time = time
        self.unit = unit
        if self.unit is not BSTime.SECOND:
            self.time = self.unit.normalize(self.time)
            self.unit = BSTime.SECOND

    def __repr__(self):
        return "{}{}".format(self.time, self.unit.name)


class UseBy(TimeConstraint):

    def __init__(self, time: float, unit: BSTime):
        super().__init__(IRInstruction.USEBY, time, unit)

    def __repr__(self):
        return "USEBY {}{}".format(self.time, self.unit.value)


class ExecuteFor(TimeConstraint):

    def __init__(self, execute_for: float = 10, unit: BSTime = BSTime.SECOND):
        super().__init__(IRInstruction.EXECUTEFOR, execute_for, unit)

    def __repr__(self):
        return "EXECUTEFOR {}{}".format(self.time, self.unit.value)
