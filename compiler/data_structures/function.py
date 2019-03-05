class Function(object):

    def __init__(self, name: str, return_types, args, return_size: int = 1):
        self.name = name
        self.types = return_types
        self.args = args
        self.return_size = return_size

    def __str__(self):
        output = "\t["
        if self.types:
            for t in self.types:
                output += "{}, ".format(t)
            output = output[:-2]
        output += "]\t{}\t{{".format(self.name)
        if self.args:
            for arg in self.args:
                output += "{}, ".format(arg.name)
            output = output[:-2]
        output += "}"
        return output

    def __repr__(self):
        return self.__str__()
