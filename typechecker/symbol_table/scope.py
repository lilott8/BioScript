

class Scope(object):

    def __init__(self, name, parent=""):
        self.name = name
        self.parent = parent
        self.locals = dict()

    def add_local(self, local):
        self.locals[local['name']] = local

    def get_name(self):
        return self.name

    def get_parent(self):
        return self.parent

    def get_locals(self):
        return self.locals
