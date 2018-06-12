from enum import Enum


class Problem(Enum):
    STORAGE = 100
    DISPOSAL = 10
    MIX = 0

#python enum is called by: x = Consequence(Consequence.H)
class Consequence(Enum):
    H   = 0
    F   = 1
    G   = 2
    GT  = 3
    GF  = 4
    E   = 5
    P   = 6
    S   = 7
    U   = 8
    WRS = 9
    N   = 10
    C   = 11
    SR  = 12

    def __init__(self, Type):
        self.value = Type

    #toString() from Java, if you will...
    def __str__(self):
        if self.value == Consequence.H:
            return "Head Generation"
        elif self.value == Consequence.F:
            return "Fire"
        elif self.value == Consequence.G:
            return "Innocuous and non-Flammable Gas generation"
        elif self.value == Consequence.GT:
            return "Toxic Gas Formation"
        elif self.value == Consequence.GF:
            return "Flammable Gas Formation"
        elif self.value == Consequence.E:
            return "Explosion"
        elif self.value == Consequence.P:
            return "Violent Polymerization"
        elif self.value == Consequence.S:
            return "Solubilization of Toxic Substance"
        elif self.value == Consequence.U:
            return "Unknown"
        elif self.value == Consequence.WRS:
            return "Water Reactive Substance"
        elif self.value == Consequence.N:
            return "Incompatible"
        elif self.value == Consequence.C:
            return "Caution"
        elif self.value == Consequence.SR:
            return "Self Reactive"
        else:
            return "????"


#dummy function for now...
def get_type_from_id(x):
    return x


