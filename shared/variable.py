from shared.enums.chemtypes import ChemTypes


class Variable(object):

    def __init__(self, name: str, types: frozenset = None, scope: str = "unknown", size=1,
                 stationary: bool = False, is_global: bool = False):
        self.name = name
        self.types = types
        self.scope = scope
        self.size = size
        self.is_declared = False
        self.is_stationary = stationary
        self.is_global = is_global
        if self.types is None:
            self.types = set()
            self.types.add(ChemTypes.UNKNOWN)

    def __repr__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}".format(self.name)
        output += "\tsize: {}".format(self.size)
        output += "\t({})".format(self.scope)
        return output
