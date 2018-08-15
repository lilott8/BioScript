class Variable(object):

    def __init__(self, name, types=None, scope="unknown", is_array=False):
        self.name = name
        self.types = types
        self.scope = scope
        self.is_array = is_array
        self.is_declared = False

    def __str__(self):
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
