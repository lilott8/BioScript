from abc import ABC


class Variable(object):

    def __init__(self, name: str, types: set() = None, scope: str = "unknown", is_array: bool = False):
        self.name = name
        self.types = types
        self.scope = scope
        self.is_array = is_array
        self.is_declared = False

    def __repr__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}".format(self.name)
        if self.is_array:
            output += "[]"
        output += "\t({})".format(self.scope)
        return output


class Array(Variable):

    def __init__(self, name: str, types: frozenset = None, scope: str = "unknown", size: int = 2):
        super().__init__(name, types, scope, True)
        self.size = size
