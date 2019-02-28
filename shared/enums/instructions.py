from enum import IntEnum


class Instruction(IntEnum):
    MIX = 0
    SPLIT = 1
    DETECT = 2
    DISPENSE = 4
    DISPOSE = 8
    HEAT = 16
    METHOD = 32
    EXPRESSION = 64
    CONDITIONAL = 128
    JUMP = 256
    LABEL = 512


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
    EQUAL = 0
    NE = 1
    LT = 2
    LTE = 3
    GT = 4
    GTE = 5


class InstructionSet(object):
    instructions = {Instruction.MIX, Instruction.SPLIT, Instruction.DETECT, Instruction.DISPENSE,
                    Instruction.DISPOSE, Instruction.HEAT, Instruction.METHOD, Instruction.EXPRESSION}

    BinaryOps = {BinaryOps.AND, BinaryOps.ADD, BinaryOps.DIVIDE, BinaryOps.MULTIPLE, BinaryOps.OR, BinaryOps.SUBTRACT}
