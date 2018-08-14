from bioscript.visitors.bs_base_visitor import BSBaseVisitor


class TypeCheckVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table)
        self.problem = None
