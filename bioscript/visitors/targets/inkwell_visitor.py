from bioscript.visitors.targets.mfsim_visitor import MFSimVisitor


class InkwellVisitor(MFSimVisitor):

    def __init__(self, symbol_table, name="InkwellVisitor"):
        super().__init__(symbol_table, name)
