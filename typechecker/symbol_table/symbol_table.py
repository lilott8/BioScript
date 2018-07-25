from typechecker.symbol_table.scope import Scope


class SymbolTable(object):

    def __init__(self):
        self.scope_stack = list()
        self.scope_map = dict()
        self.current_scope = Scope("main")
        self.scope_stack.append(self.current_scope)
        self.scope_map[self.current_scope.get_name()] = self.current_scope

    def add_new_scope(self, name):
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.scope_stack.append(self.current_scope)
        self.current_scope = Scope(name)

    def end_scope(self):
        self.scope_map[self.current_scope.get_name()] = self.current_scope
        self.current_scope = self.scope_stack.pop()

    def add_local(self, local):
        self.current_scope.add_local(local)

    def add_parent(self, parent):
        self.current_scope.set_parent(parent)
