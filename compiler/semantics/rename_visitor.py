from compiler.semantics.bs_base_visitor import BSBaseVisitor


class RenameVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, name="RenameVisitor")
