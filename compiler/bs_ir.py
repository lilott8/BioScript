from compiler.registers import *
from shared.enums.instructions import *
from shared.function import Function


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


class Temp(Expression):
    def __init__(self, value: Variable):
        super().__init__(IRInstruction.TEMP)
        self.value = value


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
        self.reagents = []
        self.register = out
        self.execute_for = ExecuteFor(execute_for[0], execute_for[1])
        self.use_by = None
        if use_by:
            self.use_by = UseBy(use_by[0], use_by[1])

    def __str__(self):
        return "{}: out-register: {}".format(super().__str__(), self.register)


class Mix(Statement):
    def __init__(self, out: Temp, one: Temp, two: Temp,
                 execute_for: (float, BSTime) = (10, BSTime.SECOND), use_by: (float, BSTime) = None):
        super().__init__(IRInstruction.MIX, out, execute_for, use_by)
        self.reagents.extend([one, two])


class Split(Statement):
    def __init__(self, out: Temp, one: Temp, size: int, execute_for: (float, BSTime) = (-1, BSTime.SECOND),
                 use_by: (float, BSTime) = None):
        super().__init__(IRInstruction.SPLIT, out, execute_for, use_by=use_by)
        self.reagents.append(one)
        self.size = size


class Detect(Statement):
    def __init__(self, module: Temp, out: Temp, execute_for: (float, BSTime)):
        super().__init__(IRInstruction.DETECT, out, execute_for)
        self.module = module


class Heat(Statement):
    def __init__(self, out: Temp, reagent: Temp, execute_for: (float, BSTime),
                 use_by: (float, BSTime) = None, heat_for: (float, BSTime) = (10, BSTime.SECOND)):
        super().__init__(IRInstruction.HEAT, out, execute_for, use_by=use_by)
        self.reagents.append(reagent)
        self.time = heat_for


class Dispense(Statement):
    def __init__(self, out: Temp, reagent: Temp):
        super().__init__(IRInstruction.DISPENSE, out)
        self.reagents.append(reagent)


class Dispose(Statement):
    def __init__(self, out: Output, reagent: Temp):
        super().__init__(IRInstruction.DISPOSE, out)
        self.reagents.append(reagent)


class Store(Statement):
    def __init__(self, out: Temp, value: Expression):
        super().__init__(IRInstruction.STORE, out)
        self.reagents.append(value)


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

    def __str__(self):
        return "({}{}{}) T: {}\tF:{}".format(self.left, self.relop, self.right, self.true_branch, self.false_branch)

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

    def __init__(self, op: IRInstruction, time: float, unit: BSTime):
        super().__init__(op)
        self.time = time
        self.unit = unit
        if self.unit is not BSTime.SECOND:
            self.time = self.unit.normalize(self.time)
            self.unit = BSTime.SECOND

    def __repr__(self):
        return "{}s".format(self.time)


class UseBy(Meta):

    def __init__(self, time: float, unit: BSTime):
        super().__init__(IRInstruction.USEBY, time, unit)

    def __repr__(self):
        return "USEBY {}".format(super.__repr__())


class ExecuteFor(Meta):

    def __init__(self, execute_for: float = 10, unit: BSTime = BSTime.SECOND):
        super().__init__(IRInstruction.EXECUTEFOR, execute_for, unit)

    def __repr__(self):
        return "EXECUTEFOR {}".format(super.__repr__())
