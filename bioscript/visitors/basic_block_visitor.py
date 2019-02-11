from bioscript.visitors.bs_base_visitor import BSBaseVisitor


class BasicBlockVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        self.basic_blocks = list()
