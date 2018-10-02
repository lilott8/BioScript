class Variable(object):

    def __init__(self, name: str, types: set() = None, scope: str = "unknown", is_array: bool = False):
        self.name = name
        self.types = types
        self.scope = scope
        self.is_array = is_array
        self.is_declared = False

    def get_size(self) -> int:
        raise NotImplementedError

    def __repr__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}".format(self.name)
        output += "\t({})".format(self.scope)
        return output


class Scalar(Variable):
    def __init__(self, name: str, types: frozenset = None, scope: str = "unknown"):
        super().__init__(name, types, scope, False)

    def get_size(self) -> int:
        return 0

    def __repr__(self):
        output = "Scalar value: \n"
        output += super().__repr__()


class Array(Variable):

    def __init__(self, name: str, types: frozenset = None, scope: str = "unknown", size: int = 2):
        super().__init__(name, types, scope, True)
        self.size = size

    def get_size(self) -> int:
        return self.size

    def __repr__(self):
        output = "Array[{}]: ".format(self.size)
        output += super().__repr__()
        return output
