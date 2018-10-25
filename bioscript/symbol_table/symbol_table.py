import colorlog

from bioscript.symbol_table.scope import Scope
from shared.enums.chemtypes import ChemTypes
from shared.function import Function
from shared.variable import Variable


class SymbolTable(object):

    def __init__(self, name="main"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.current_scope = Scope(name)
        self.scope_stack = list()
        self.scope_map = dict()
        self.functions = dict()
        self.globals = dict()
        self.scope_map[self.current_scope.name] = self.current_scope

    def add_new_scope(self, name: str) -> None:
        self.scope_stack.append(self.current_scope)
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.current_scope = Scope(name)

    def end_scope(self) -> None:
        # Save the current stack first.
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.current_scope = self.scope_stack.pop()

    def add_local(self, local: Variable) -> None:
        self.current_scope.add_local(local)

    def add_global(self, local: Variable) -> None:
        self.globals[local.name] = local

    def add_parent(self, parent) -> None:
        self.current_scope.set_parent(parent)

    def add_function(self, func: Function) -> None:
        self.functions[func.name] = func

    def update_symbol_by_var(self, variable: Variable) -> None:
        self.update_symbol(variable.name, variable.types)

    def update_symbol(self, name: str, types: frozenset) -> None:
        # This should only ever be local.
        # We cannot change the way globals work.
        variable = self.get_local(name)
        if not variable:
            return
        if ChemTypes.UNKNOWN in variable.types:
            variable.types.remove(ChemTypes.UNKNOWN)
        if ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION in variable.types:
            variable.types.remove(ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION)
        variable.types = variable.types.union(types)
        self.current_scope.add_local(variable)

    def get_local(self, name, scope_name: str = False) -> Variable:
        # Check for scope.
        if scope_name is not False:
            scope = self.scope_map[scope_name]
        else:
            scope = self.current_scope
        # Now that we have the scope, get the local.
        if name in scope.get_locals():
            return scope.get_locals()[name]
        elif name in self.globals:
            return False
        else:
            # self.log.fatal("No local variable found: {}".format(name))
            return False

    def get_global(self, name: str) -> Variable:
        if name in self.globals:
            return self.globals[name]
        else:
            #self.log.fatal("No global variable found: {}".format(name))
            return False

    def is_global(self, var: Variable) -> bool:
        return var.name in self.globals

    def get_variable(self, variable: str, scope_name=False) -> Variable:
        # Check for scope.
        if scope_name is not False:
            scope = self.scope_map[scope_name]
        else:
            scope = self.current_scope
        # Now check for the variable.
        if variable in self.globals:
            return self.globals[variable]
        elif variable in scope.get_locals():
            return scope.get_locals()[variable]
        else:
            self.log.fatal("No variable found: {} in {}".format(variable, scope.name))
            return False

    def __repr__(self):
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
