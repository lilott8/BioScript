from compiler.data_structures.variable import Symbol


class Scope(object):
    """
    This represents a scope -- the place to where
    variables are bound.  In this environment,
    there are only function-level scoping.
    All programs begin with a "main" function.
    Because scoping only occurs at the function level,
    there is no hierarchy to the scope -- it's all flat.
    """

    def __init__(self, name):
        self.name = name
        self.locals = dict()

    def add_local(self, local: Symbol):
        """
        Adds a local variable to the scope.
        :param local: Variable that belongs to this scope.
        :return: None
        """
        if local.name not in self.locals:
            self.locals[local.name] = local
        else:
            self.locals[local.name].types.update(local.types)

    def __str__(self):
        output = ""
        for var in self.locals:
            output += "\t{}\n".format(self.locals[var])
        return output
