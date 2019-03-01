class BSProgram(object):
    """
    This class models the input program and
    stores various data about the program.
    """

    def __init__(self, ir: 'IRVisitor'):
        # A dict: id->basic block
        self.functions = ir.functions
        # Set of basic block ids that are roots
        self.roots = ir.roots
        # The main entry point for the program
        self.entry_point = ir.entry_block
        # The symbol table for the program
        self.symbol_table = ir.symbol_table
        # The basic block based control flow graph
        self.bb_graph = ir.graph
        # The name of the graph
        self.name = None
        # Is this program in SSA form?
        self.ssa_form = False
        # Storing different analysis here (liveness, call graph, etc)
        self.analysis = dict()
