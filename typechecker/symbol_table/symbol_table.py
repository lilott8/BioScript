from typechecker.symbol_table.scope import Scope
import colorlog
from shared.enums.chemtypes import ChemTypes


class SymbolTable(object):

    def __init__(self, name="main"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.current_scope = Scope(name)
        self.scope_stack = list()
        self.scope_map = dict()
        self.functions = dict()
        self.globals = dict()

    def add_new_scope(self, name):
        self.scope_stack.append(self.current_scope)
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.current_scope = Scope(name)

    def end_scope(self):
        # Save the current stack first.
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.current_scope = self.scope_stack.pop()

    def add_local(self, local):
        self.current_scope.add_local(local)

    def add_global(self, local):
        self.globals[local.name] = local

    def add_parent(self, parent):
        self.current_scope.set_parent(parent)

    def add_function(self, func):
        self.functions[func.name] = func

    def update_symbol_by_var(self, variable):
        self.update_symbol(variable.name, variable.types)

    def update_symbol(self, name, types):
        # This should only ever be local.
        # We cannot change the way globals work.
        variable = self.get_local(name)
        if not variable:
            return
        if ChemTypes.UNKNOWN in variable.types:
            variable.types.remove(ChemTypes.UNKNOWN)
        variable.types = variable.types.union(types)
        self.current_scope.add_local(variable)

    def get_local(self, name):
        if name in self.current_scope.get_locals():
            return self.current_scope.get_locals()[name]
        elif name in self.globals:
            return False
        else:
            self.log.fatal("No local variable found: {}".format(name))
            return False

    def get_global(self, name):
        if name in self.globals:
            return self.globals[name]
        else:
            self.log.fatal("No global variable found: {}".format(name))
            return False

    def get_variable(self, variable):
        if variable in self.globals:
            return self.globals[variable]
        elif variable in self.current_scope.get_locals():
            return self.current_scope.get_locals()[variable]
        else:
            self.log.fatal("No variable found: {}".format(variable))
            return False

    def __str__(self):
        output = "[GLOBALS]:\n"
        for glob in self.globals:
            output += "{}\n".format(self.globals[glob])
        for func in self.functions:
            output += "[FUNCTION {}]:\n".format(func)
            output += "{}\n".format(self.functions[func])
        for scope in self.scope_map:
            output += "[SCOPE: {}]:\n".format(scope)
            output += "{}\n".format(self.scope_map[scope])
        return output