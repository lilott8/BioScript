from abc import ABCMeta, abstractmethod
from enum import IntEnum
from typing import Dict, List

from compiler.data_structures.function import Function
from compiler.data_structures.properties import BSTime, BSTemperature


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

    def get_string(self):
        if self.value == BinaryOps.ADD:
            return "+"
        elif self.value == BinaryOps.SUBTRACT:
            return "-"
        elif self.value == BinaryOps.MULTIPLE:
            return "*"
        elif self.value == BinaryOps.DIVIDE:
            return "/"
        elif self.value == BinaryOps.OR:
            return "||"
        elif self.value == BinaryOps.AND:
            return "&&"
        else:
            return "+"


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
                  IRInstruction.CALL, IRInstruction.MATH, IRInstruction.GRADIENT, IRInstruction.DETECT,
                  IRInstruction.PHI}

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
        self.uses = list()
        self.defs = None
        self.meta = list()

    @abstractmethod
    def expand(self) -> List:
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

    def expand(self) -> List:
        return [self]


"""
========================================================
Expression IR:
    Deals with computation of some value
========================================================
"""


class Expression(IR, metaclass=ABCMeta):

    def __init__(self, op: IRInstruction):
        super().__init__(op)

    def expand(self) -> List:
        return [self]


class Constant(Expression):
    def __init__(self, out: Dict, value: float):
        super().__init__(IRInstruction.CONSTANT)
        self.value = value
        self.defs = out

    def expand(self) -> List:
        ret = list()
        if self.defs['size'] > 1 and self.defs['offset'] == -1:
            for x in range(self.defs['size']):
                ret.append(Constant({'name': self.defs['name'], 'offset': x,
                                     'size': self.defs['size'], 'var': self.defs['var']},
                                    self.value[x]))
        else:
            ret.append(Constant({'name': self.defs['name'], 'offset': 0, 'size': 1, 'var': self.defs['var']},
                                self.value[0]))
        return ret

    def __str__(self):
        return "CONSTANT: {}".format(self.value)

    def __repr__(self):
        return self.__str__()


class Math(Expression):
    def __init__(self, out: Dict, op1: Dict, op2: Dict, operand: BinaryOps):
        super().__init__(IRInstruction.MATH)
        self.uses.extend([op1, op2])
        self.operand = operand
        self.defs = out


class BinaryOp(Expression):
    def __init__(self, left: Dict, right: Dict, op: RelationalOps):
        super().__init__(IRInstruction.BINARYOP)
        self.left = left
        self.right = right
        self.op = op
        self.uses.extend([left, right])


class Call(Expression):
    def __init__(self, out: Dict, func: Function, arguments: list):
        super().__init__(IRInstruction.CALL)
        self.function = func
        self.args = self.function.args
        self.name = self.function.name
        self.uses = arguments
        self.defs = out
        self.label = Label(self.function.name)

    def __str__(self):
        return "{} = {}({})".format(self.defs.name, self.function.name, self.uses)

    def __repr__(self):
        return self.__str__()


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


class Statement(IR, metaclass=ABCMeta):
    def __init__(self, op: IRInstruction, out):
        super().__init__(op)
        self.defs = out

    def __str__(self):
        return "\n".join(str(s) for s in self.meta)


class Mix(Statement):
    def __init__(self, out: Dict, one: Dict, two: Dict):
        super().__init__(IRInstruction.MIX, out)
        self.uses.extend([one, two])

    def expand(self) -> List:
        ret = []
        use_a = self.uses[0]
        use_b = self.uses[1]
        '''
                Cases that need to be considered:
                1) a = dispense aaa
                    b = dispense bbb
                    c = mix(a, b)
                    (all indices are -1 *and* size = 1)

                2) a[n] = dispense aaa
                    b[m] = dispense bbb
                    c = mix(a[x], b[y]) 
                    (index(c) == -1, index(a) == x, index(b) == y, *and* size = 1)

                3) a[n] = dispense aaa
                    b[n] = dispense bbb
                    c = mix(a, b) 
                    (index(c) == -1, index(a) == -1, index(b) == -1, *and* size(a || b) == length(a || b))
        '''
        if self.defs['size'] > 1 and self.defs['offset'] == -1:
            for x in range(self.defs['size']):
                use_a['offset'] = x
                use_b['offset'] = x
                ret.append(Mix({'name': self.defs['name'], 'offset': x, 'size': self.defs['size'],
                                'var': self.defs['var']},
                               {'name': use_a['name'], 'offset': x,
                                'size': use_a['size'], 'var': use_a['var']},
                               {'name': use_b['name'], 'offset': x,
                                'size': use_b['size'], 'var': use_b['var']}
                               ))
                # Always save the meta operations.
                ret[-1].meta = self.meta
        else:
            def_offset = 0 if self.defs['size'] == 1 and self.defs['offset'] == -1 else self.defs['offset']

            use_a_offset = 0 if use_a['offset'] == -1 else use_a['offset']
            use_b_offset = 0 if use_b['offset'] == -1 else use_b['offset']
            ret.append(Mix({'name': self.defs['name'], 'offset': def_offset,
                            'size': self.defs['size'], 'var': self.defs['var']},
                           {'name': use_a['name'], 'offset': use_a_offset,
                            'size': use_a['size'], 'var': use_a['var']},
                           {'name': use_b['name'], 'offset': use_b_offset,
                            'size': use_b['size'], 'var': use_b['var']}
                           ))
            ret[-1].meta = self.meta
        return ret

    def __str__(self):
        return "{}[{}] = mix({}[{}], {}[{}])".format(self.defs['name'], self.defs['offset'],
                                                     self.uses[0]['name'], self.uses[0]['offset'],
                                                     self.uses[1]['name'], self.uses[1]['offset'])


class Split(Statement):
    def __init__(self, out: Dict, one: Dict, split_num: int):
        super().__init__(IRInstruction.SPLIT, out)
        self.uses.append(one)
        self.split_size = split_num

    def expand(self) -> List:
        return [self]

    def __str__(self):
        return "SPLIT: {}[{}] = split({}, {})".format(self.defs['name'], self.defs['offset'], self.uses[0]['name'],
                                                      self.defs['offset'])


class Detect(Statement):
    def __init__(self, out: Dict, module: Dict, one: Dict):
        super().__init__(IRInstruction.DETECT, out)
        self.uses.extend([module, one])

    def expand(self) -> List:
        ret = []
        module = self.uses[0]
        use = self.uses[1]
        if self.defs['size'] > 1 and self.defs['offset'] == -1:
            for x in range(self.defs['size']):
                module['offset'] = x
                use['offset'] = x
                ret.append(Detect({'name': self.defs['name'], 'offset': x, 'size': self.defs['size'],
                                'var': self.defs['var']},
                               {'name': module['name'], 'offset': x,
                                'size': module['size'], 'var': module['var']},
                               {'name': use['name'], 'offset': x,
                                'size': use['size'], 'var': use['var']}
                               ))
                # Always save the meta operations.
                ret[-1].meta = self.meta
        else:
            def_offset = 0 if self.defs['size'] == 1 and self.defs['offset'] == -1 else self.defs['offset']

            use_offset = 0 if use['offset'] == -1 else use['offset']
            ret.append(Detect({'name': self.defs['name'], 'offset': def_offset,
                            'size': self.defs['size'], 'var': self.defs['var']},
                           {'name': module['name'], 'offset': module['offset'],
                            'size': module['size'], 'var': module['var']},
                           {'name': use['name'], 'offset': use_offset,
                            'size': use['size'], 'var': use['var']}
                           ))
            ret[-1].meta = self.meta
        return ret

    def __str__(self):
        return "{}[{}] = detect({}, {}[{}])".format(self.defs['name'], self.defs['offset'], self.uses[0]['name'],
                                                    self.uses[1]['name'], self.uses[1]['offset'])


class Heat(Statement):
    def __init__(self, out: Dict, reagent: Dict):
        super().__init__(IRInstruction.HEAT, out)
        self.uses.append(reagent)

    def expand(self) -> List:
        ret = list()
        if self.defs['size'] > 1 and self.defs['offset'] == -1:
            for x in range(self.defs['size']):
                reagent = {'name': self.defs['name'], 'offset': x, 'size': self.defs['size'], 'var': self.defs['var']}
                ret.append(Heat(reagent, reagent))
                # Always save the meta operations.
                ret[-1].meta = self.meta
        else:
            offset = 0 if self.uses[0]['offset'] == -1 else self.uses[0]['offset']
            reagent = {'name': self.defs['name'], 'offset': offset, 'size': self.defs['size'], 'var': self.defs['var']}
            ret.append(Heat(reagent, reagent))
            ret[-1].meta = self.meta
        return ret

    def __str__(self):
        return f"heat({self.uses[0]['name']}[{self.uses[0]['offset']}], {super().__str__()})"


class Dispense(Statement):
    def __init__(self, out: Dict, reagent: Dict):
        super().__init__(IRInstruction.DISPENSE, out)
        self.uses.append(reagent)

    def expand(self) -> List:
        ret = list()
        usage = {'name': self.uses[0]['name'], 'offset': self.uses[0]['offset'], 'size': self.uses[0]['size']}
        if self.defs['size'] > 1 and self.defs['offset'] == -1:
            for x in range(self.defs['size']):
                ret.append(Dispense({'name': self.defs['name'], 'offset': x,
                                     'size': self.defs['size'], 'var': self.defs['var']},
                                    usage))
                # Always save the meta operations.
                ret[-1].meta = self.meta
        else:
            ret.append(Dispense({'name': self.defs['name'], 'offset': 0, 'size': 1, 'var': self.defs['var']},
                                usage))
            ret[-1].meta = self.meta
        return ret

    def __str__(self):
        return "{}[{}] = dispense({})".format(self.defs['name'], self.defs['offset'], self.uses[0]['name'])


class Dispose(Statement):
    def __init__(self, out: Dict):
        super().__init__(IRInstruction.DISPOSE, out)
        self.uses.append(out)

    def expand(self) -> List:
        ret = list()
        if self.uses[0]['size'] > 1 and self.uses[0]['offset'] == -1:
            for x in range(self.uses[0]['size']):
                ret.append(Dispose({'name': self.uses[0]['name'], 'offset': x,
                                    'size': self.uses[0]['size'], 'var': self.uses[0]['var']}))
                # Always save the meta operations.
                ret[-1].meta = self.meta
        else:
            offset = 0 if self.uses[0]['offset'] == -1 else self.uses[0]['offset']
            ret.append(Dispose({'name': self.uses[0]['name'], 'offset': offset,
                                'size': self.uses[0]['size'], 'var': self.uses[0]['var']}))
            ret[-1].meta = self.meta
        return ret

    def __str__(self):
        return "dispose({})".format(self.uses[0])


class Store(Statement):
    def __init__(self, out: Dict):
        super().__init__(IRInstruction.STORE, out)
        self.uses.append(out)
        self.defs = out

    def expand(self) -> List:
        ret = list()
        if self.defs['size'] > 1 and self.defs['offset'] == -1:
            for x in range(self.defs['size']):
                ret.append(Store({'name': self.uses[0]['name'], 'offset': x,
                                  'size': self.uses[0]['size'], 'var': self.uses[0]['var']}))
                # Always save the meta operations.
                ret[-1].meta = self.meta
        else:
            offset = 0 if self.uses[0]['offset'] == -1 else self.uses[0]['offset']
            ret.append(Store({'name': self.uses[0]['name'], 'offset': offset,
                              'size': self.uses[0]['size'], 'var': self.uses[0]['var']}))
            ret[-1].meta = self.meta
        return ret

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

    def expand(self) -> List:
        return [self]


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

    def __init__(self, relop: RelationalOps, left: Dict, right: Dict,
                 t_branch: Label = None, f_branch: Label = None):
        super().__init__(IRInstruction.CONDITIONAL)
        # first is true, last is else
        self.true_branch = t_branch
        self.false_branch = f_branch
        self.relop = relop
        self.left = left
        self.right = right
        self.uses.extend([left, right])
        self.defs = None

    def __str__(self):
        return f"Conditional:\t ({self.left['name']} {self.relop.get_readable()} {self.right['name']})\t " \
               f"T: {self.true_branch.label}\tF: {self.false_branch.label}"

    def __repr__(self):
        return self.__str__()


class Return(Control):

    def __init__(self, return_value: Dict):
        super().__init__(IRInstruction.RETURN)
        self.return_value = return_value
        self.uses = [return_value]
        self.defs = return_value


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

    def expand(self) -> List:
        return [self]


class Phi(Meta):
    def __init__(self, left: Expression, right: list):
        super().__init__(IRInstruction.PHI)
        self.defs = left
        self.uses = right

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

    def __repr__(self):
        return "{} {} {}".format(self.op.name, self.quantity, self.unit.name)

    def __str__(self):
        return self.__repr__()


class UseBy(TimeConstraint):

    def __init__(self, time: float, unit: BSTime):
        super().__init__(IRInstruction.USEBY, time, unit)

    def __repr__(self):
        return "USEBY {}{}".format(self.quantity, self.unit.value)


class ExecuteFor(TimeConstraint):

    def __init__(self, execute_for: float = 10, unit: BSTime = BSTime.SECOND):
        super().__init__(IRInstruction.EXECUTEFOR, execute_for, unit)

    def __repr__(self):
        return "EXECUTEFOR {}{}".format(self.quantity, self.unit.value)
