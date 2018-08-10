

class Function(object):

    def __init__(self, name, return_types, args):
        self.name = name
        self.types = return_types
        self.args = args

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