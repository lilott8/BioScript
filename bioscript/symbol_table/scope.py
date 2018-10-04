class Scope(object):

    def __init__(self, name, parent=""):
        # self.log = colorlog.getLogger(self.__class__.__name__)
        self.name = name
        self.parent = parent
        self.locals = dict()

    def add_local(self, local):
        if local.name not in self.locals:
            self.locals[local.name] = local
        else:
            self.locals[local.name].types.update(local.types)

    def get_name(self):
        return self.name

    def get_parent(self):
        return self.parent

    def get_locals(self):
        return self.locals

    def set_parent(self, parent):
        self.parent = parent

    def __str__(self):
        output = ""
        for var in self.locals:
            output += "\t{}\n".format(var)
        return output
