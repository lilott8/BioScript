from typing import Set

import colorlog

from compiler.data_structures.scope import Scope
from compiler.data_structures.variable import Variable


class SymbolTable(object):

    def __init__(self, name="main"):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.current_scope = Scope(name)
        self.scope_stack = list()
        self.scope_map = dict()
        self.functions = dict()
        self.globals = dict()
        self.scope_map[self.current_scope.name] = self.current_scope

    def new_scope(self, name: str) -> None:
        self.scope_stack.append(self.current_scope)
        self.scope_map[self.current_scope.name] = self.current_scope
        self.current_scope = Scope(name)
        self.scope_map[self.current_scope.name] = self.current_scope

    def end_scope(self) -> None:
        # Save the current stack first.
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.current_scope = self.scope_stack.pop()

    def update_symbol_by_var(self, variable: Variable) -> Variable:
        return self.update_symbol(variable.name, variable.types)

    def update_symbol(self, name: str, types: Set) -> Variable:
        # This should only ever be local.
        # We cannot change the way globals work.
        variable = self.get_local(name)
        if not variable:
            return
        variable.types = variable.types.union(types)
        self.current_scope.add_local(variable)
        return variable

    def get_local(self, name: str, scope_name: str = False) -> Variable:
        # Check for scope.
        scope = self.current_scope if scope_name is False else self.scope_map[scope_name]
        # Now that we have the scope, get the local.
        if name in scope.locals:
            return scope.locals[name]
        else:
            # self.log.fatal("No local variable found: {}".format(name))
            return None

    def add_local(self, var: Variable):
        """
        Add a variable to the current scope.
        This always assumes the current scope.
        :param var: Variable to be added.
        :return: None.
        """
        self.current_scope.add_local(var)

    def add_local_to_scope(self, var: Variable, scope_name: str):
        """
        Add a local variable to a different scope.
        :param var: Variable to be added.
        :param scope_name: The name of scope to add the variable.
        :return: None.
        """
        self.scope_map[scope_name].add_local(var)

    def get_global(self, name: str) -> Variable:
        if name in self.globals:
            return self.globals[name]
        else:
            return None

    def add_global(self, var: Variable) -> None:
        self.globals[var.name] = var

    def is_global(self, var: str) -> bool:
        return var in self.globals

    def get_variable(self, variable: str, scope_name: str = False) -> Variable:
        # Check for scope.
        scope = self.current_scope if scope_name is False else self.scope_map[scope_name]
        # Now check for the variable.
        if variable in self.globals:
            return self.globals[variable]
        elif variable in scope.locals:
            return scope.locals[variable]
        else:
            self.log.fatal("No variable found: {} in {}".format(variable, scope.name))
            return None

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
