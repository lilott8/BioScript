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
