import colorlog

from compiler.data_structures.scope import Scope
from compiler.data_structures.variable import Symbol


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
        self.scope_map[self.current_scope.name] = self.current_scope
        self.current_scope = self.scope_stack.pop()

    def update_symbol(self, symbol: Symbol) -> Symbol:
        self.current_scope.locals[symbol.name] = symbol
        return symbol

    def get_local(self, name: str, scope_name: str = False) -> Symbol:
        # Check for scope.
        scope = self.current_scope if scope_name is False else self.scope_map[scope_name]
        # Now that we have the scope, get the local.
        if name in scope.locals:
            return scope.locals[name]
        else:
            # self.log.fatal("No local variable found: {}".format(name))
            return None

    def add_local(self, symbol: Symbol):
        """
        Add a variable to the current scope.
        This always assumes the current scope.
        :param symbol: Variable to be added.
        :return: None.
        """
        self.current_scope.add_local(symbol)

    def add_local_to_scope(self, symbol: Symbol, scope_name: str):
        """
        Add a local variable to a different scope.
        :param symbol: Variable to be added.
        :param scope_name: The name of scope to add the variable.
        :return: None.
        """
        self.scope_map[scope_name].add_local(symbol)

    def get_global(self, name: str) -> Symbol:
        if name in self.globals:
            return self.globals[name]
        else:
            return None

    def add_global(self, symbol: Symbol) -> None:
        self.globals[symbol.name] = symbol

    def is_global(self, var: str) -> bool:
        return var in self.globals

    def get_symbol(self, symbol: str, scope_name: str = False) -> Symbol:
        """
        A wrapper method to get a symbol from
        either the current scope or the global scope.
        :param symbol: The symbol to look for.
        :param scope_name: The scope name to look in.
        :return: The requested symbol.
        """
        # Check for scope.
        scope = self.current_scope if scope_name is False else self.scope_map[scope_name]
        # Now check for the variable.
        if symbol in self.globals:
            return self.globals[symbol]
        elif symbol in scope.locals:
            return scope.locals[symbol]
        else:
            self.log.fatal("No variable found: {} in {}".format(symbol, scope.name))
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
