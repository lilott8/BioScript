from abc import ABCMeta, abstractmethod
from enum import IntEnum
from typing import Dict

from compiler.data_structures.function import Function
from compiler.data_structures.properties import BSTime, BSTemperature
from compiler.data_structures.variable import Variable


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
    GRADIENT = 12
    # Control
    JUMP = 13
    CONDITIONAL = 14
    LABEL = 15
    RETURN = 16
    # Meta
    USEBY = 17
    EXECUTEFOR = 18
    NOP = 19
    PHI = 20
    TIME = 21
    TEMPERATURE = 22
    MATH = 23



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


class InstructionSet(metaclass=ABCMeta):
    instructions = {IRInstruction.MIX, IRInstruction.SPLIT, IRInstruction.DETECT, IRInstruction.DISPENSE,
                    IRInstruction.DISPOSE, IRInstruction.HEAT, IRInstruction.CALL, IRInstruction.BINARYOP,
                    IRInstruction.GRADIENT}

    assignment = {IRInstruction.MIX, IRInstruction.SPLIT, IRInstruction.SPLIT, IRInstruction.DISPENSE,
                  IRInstruction.CALL, IRInstruction.MATH, IRInstruction.GRADIENT, IRInstruction.DETECT}

    BinaryOps = {BinaryOps.AND, BinaryOps.ADD, BinaryOps.DIVIDE, BinaryOps.MULTIPLE, BinaryOps.OR, BinaryOps.SUBTRACT}

    control_flow = {IRInstruction.CONDITIONAL, IRInstruction.JUMP}

class IR(metaclass=ABCMeta):
    id_counter = 1

    @staticmethod
    def get_next_id():
        temp = IR.id_counter
        IR.id_counter += 1
        return temp

    def __init__(self, op: IRInstruction):
        self.op = op
        self.name = op.name
        self.iid = IR.get_next_id()

    @abstractmethod
    def write(self, target: 'BaseTarget') -> str:
        pass

    def __repr__(self):
        return self.name

    def __str__(self):
        return self.name


class NOP(IR):
    def __init__(self):
        super().__init__(IRInstruction.NOP)
        self.uses = []
        self.defs = None

    def write(self, target: 'BaseTarget') -> str:
        return ""


"""
========================================================
Expression IR:
    Deals with computation of some value
========================================================
"""


class Expression(IR, ABCMeta, metaclass=ABCMeta):

    def __init__(self, op: IRInstruction):
        super().__init__(op)

    def write(self, target: 'BaseTarget') -> str:
        pass


class Constant(Expression):
    def __init__(self, value: float):
        super().__init__(IRInstruction.CONSTANT)
        self.value = value

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "CONSTANT: {}".format(self.value)

    def __repr__(self):
        return self.__str__()


class BinaryOp(Expression):
    def __init__(self, left: Expression, right: Expression, op: BinaryOps, out: Dict):
        super().__init__(IRInstruction.BINARYOP)
        self.left = left
        self.right = right
        self.op = op
        self.uses = [x for x in [left, right] if isinstance(x, Variable)]
        #self.uses = [out ,left, right]
        self.defs = out

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "BINARYOP {} {} {} {}".format(self.defs, self.op, self.left, self.right)


class Call(Expression):
    def __init__(self, out: Dict, func: Function, arguments: list):
        super().__init__(IRInstruction.CALL)
        self.function = func
        self.args = self.function.args
        self.name = self.function.name
        self.uses = arguments
        self.defs = out

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "{} = {}({})".format(self.defs.name, self.function.name, self.uses)

    def __repr__(self):
        return self.__str__()


class Name(Expression):
    def __init__(self, name: str):
        super().__init__(IRInstruction.NAME)
        self.name = name

    def write(self, target: 'BaseTarget') -> str:
        pass


"""
========================================================
Statement IR:
    Operations that move the program from one state
    to another.  This includes instructions that
    can mutate the store.
========================================================
"""


class Statement(IR, metaclass=ABCMeta):
    def __init__(self, op: IRInstruction, out):
        super().__init__(op)
        self.uses = []
        self.defs = out
        self.meta = list()

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "\n".join(str(s) for s in self.meta)


class Mix(Statement):
    def __init__(self, out: Dict, one: Dict, two: Dict):
        super().__init__(IRInstruction.MIX, out)
        self.uses.extend([one, two])

    def write(self, target: 'BaseTarget') -> str:
        return target.write_mix(self)

    def __str__(self):
        return "{}[{}] = mix({}[{}], {}[{}])".format(self.defs['name'], self.defs['offset'],
                                                     self.uses[0]['name'], self.uses[0]['offset'],
                                                     self.uses[1]['name'], self.uses[1]['offset'])


class Split(Statement):
    def __init__(self, out: Dict, one: Dict, split_num: int):
        super().__init__(IRInstruction.SPLIT, out)
        self.uses.append(one)
        self.split_size = split_num

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "SPLIT: {}[{}] = split({}, {})".format(self.defs, self.defs.index, self.uses, self.defs.index)


class Detect(Statement):
    def __init__(self, out: Dict, module: Dict, one: Dict):
        super().__init__(IRInstruction.DETECT, out)
        # self.module = module
        self.uses.append(module)
        self.uses.append(one)

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "{}[{}] = detect({}, {}[{}])".format(self.defs['name'], self.defs['offset'], self.uses[0]['name'],
                                                    self.uses[1]['name'], self.uses[1]['offset'])


class Heat(Statement):
    def __init__(self, out: Dict, reagent: Dict):
        super().__init__(IRInstruction.HEAT, out)
        self.uses.append(reagent)

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        output = super().__str__() + "\n"
        output += "heat({}[{}])".format(self.uses[0]['name'], self.uses[0]['offset'])
        return output


class Dispense(Statement):
    def __init__(self, out: Dict, reagent: Dict):
        super().__init__(IRInstruction.DISPENSE, out)
        self.uses.append(reagent)

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "{}[{}] = dispense({})".format(self.defs['name'], self.defs['offset'], self.uses[0]['name'])


class Dispose(Statement):
    def __init__(self, out: Dict, reagent: Dict):
        super().__init__(IRInstruction.DISPOSE, out)
        self.uses.append(reagent)

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "dispose({})".format(self.uses[0])


class Store(Statement):
    def __init__(self, out: Dict, value: Expression):
        super().__init__(IRInstruction.STORE, out)
        if not isinstance(value, float) and value.op == IRInstruction.CALL:
            self.uses.extend(value.uses)
        self.defs = out

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "STORE:\t {} = {}".format(self.defs, self.uses)


"""
========================================================
Control IR:
    Operations that can move control of the program
    from one place to another.
========================================================
"""


class Control(IR, metaclass=ABCMeta):
    def __init__(self, op: IRInstruction):
        super().__init__(op)

    def write(self, target: 'BaseTarget') -> str:
        pass


class Label(Control):

    def __init__(self, name: str):
        super().__init__(IRInstruction.LABEL)
        self.label = name

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "LABEL: " + self.label

    def __repr__(self):
        return self.__str__()


class Jump(Control):

    def __init__(self, jump_to: Label):
        super().__init__(IRInstruction.JUMP)
        # first is true, last is else
        self.jumps = jump_to

    def write(self, target: 'BaseTarget') -> str:
        pass

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
        self.uses = [x for x in [right, left] if isinstance(x, Variable)]
        self.defs = None

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        return "CONDITIONAL:\t ({} {} {}) T: {}\tF:{}".format(self.left.name, self.relop.get_readable(),
                                                              self.right.name, self.true_branch,
                                                              self.false_branch)

    def __repr__(self):
        return self.__str__()


class Return(Control):

    def __init__(self, return_value: Expression, return_to: Label):
        super().__init__(IRInstruction.RETURN)
        self.return_value = return_value
        self.return_to = return_value
        self.uses = [return_value]
        self.defs = return_value

    def write(self, target: 'BaseTarget') -> str:
        pass


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

    def write(self, target: 'BaseTarget') -> str:
        pass


class Phi(Meta):
    def __init__(self, left: Expression, right: list):
        super().__init__(IRInstruction.PHI)
        self.defs = left
        self.uses = right

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __str__(self):
        out = "PHI:\t {} = Phi(".format(self.defs)
        temp = ""
        for r in self.uses:
            temp += "{}, ".format(r)
        temp = temp[:-2]
        out += temp + ")"
        return out


class TimeConstraint(Meta):
    def __init__(self, op: IRInstruction, time: float = 10, unit: BSTime = BSTime.SECOND):
        super().__init__(op)
        self.quantity = time
        self.unit = unit
        if self.unit is not BSTime.SECOND:
            self.quantity = self.unit.normalize(self.quantity)
            self.unit = BSTime.SECOND

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __repr__(self):
        return "{}{}".format(self.quantity, self.unit.name)


class TempConstraint(Meta):
    def __init__(self, op: IRInstruction, temp: float = 10, unit: BSTemperature = BSTemperature.CELSIUS):
        super().__init__(op)
        self.unit = unit
        self.quantity = temp
        if self.unit is not BSTemperature.CELSIUS:
            self.quantity = self.unit.normalize(self.quantity)
            self.unit = BSTemperature.CELSIUS

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __repr__(self):
        return "{} {} {}".format(self.op.name, self.quantity, self.unit.name)

    def __str__(self):
        return self.__repr__()


class UseBy(TimeConstraint):

    def __init__(self, time: float, unit: BSTime):
        super().__init__(IRInstruction.USEBY, time, unit)

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __repr__(self):
        return "USEBY {}{}".format(self.quantity, self.unit.value)


class ExecuteFor(TimeConstraint):

    def __init__(self, execute_for: float = 10, unit: BSTime = BSTime.SECOND):
        super().__init__(IRInstruction.EXECUTEFOR, execute_for, unit)

    def write(self, target: 'BaseTarget') -> str:
        pass

    def __repr__(self):
        return "EXECUTEFOR {}{}".format(self.quantity, self.unit.value)
