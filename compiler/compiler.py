import colorlog
from antlr4 import *

from compiler.data_structures.bs_program import BSProgram
from compiler.data_structures.symbol_table import SymbolTable
from compiler.passes.pass_manager import PassManager
from compiler.semantics.global_visitor import GlobalVariableVisitor
from compiler.semantics.ir_visitor import IRVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.symbol_visitor import SymbolTableVisitor
from compiler.semantics.type_visitor import TypeCheckVisitor
from compiler.targets.target_manager import TargetManager
from config.config import Config
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from shared.enums.config_flags import TypeCheckLevel
from solvers.z3_solver import Z3Solver


class BSCompiler(object):

    def __init__(self):
        self.config = Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.warning(self.config.input)
        # The symbol is built is phases, hence it's globalness.
        self.symbol_table = None
        self.program = None

    def compile(self):
        ir = self.translate(self.config.input)
        ir = self.optimizations(self.program)
        target = self.target(self.program)

    def translate(self, filename: str) -> BSProgram:
        """
        Translates the program from the AST into the corresponding IR.
        :param filename: name of file to parse.
        :return:
        """
        file_stream = FileStream(filename)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        tree = parser.program()

        # This gets run first, gathering all the globals.
        global_visitor = GlobalVariableVisitor(SymbolTable())
        global_visitor.visit(tree)

        # Build the functions and their symbols next.
        method_visitor = MethodVisitor(global_visitor.symbol_table)
        method_visitor.visit(tree)

        # Finish building the symbol table.
        symbol_visitor = SymbolTableVisitor(method_visitor.symbol_table)
        symbol_visitor.visit(tree)

        # Attempt to type check the program
        self.visit_type_check(tree, symbol_visitor.symbol_table)

        # Convert the AST to the IR for further analysis.
        ir_visitor = IRVisitor(symbol_visitor.symbol_table)
        ir_visitor.visit(tree)
        # Always update the symbol table.
        self.program = BSProgram(ir_visitor)
        self.program.name = filename

        # pos = nx.nx_agraph.graphviz_layout(ir_visitor.graph)
        # nx.draw(ir_visitor.graph, pos=pos)
        # write_dot(ir_visitor.graph, 'file.dot')

        return self.program

    def optimizations(self, program: BSProgram):
        """
        Run the various optimizations that can be run.
        :param program:
        :return:
        """
        passes = PassManager(self.program)
        passes.run_analysis()
        passes.run_transformations()
        # return passes
        return program

    def target(self, program: BSProgram):
        """
        Run the various transforms that can be run.
        :param program:
        :return:
        """
        target = TargetManager(program, self.config.target)
        target.transform()
        return target

    def visit_type_check(self, tree, symbol_table: SymbolTable):
        """
        Attempts to typecheck a program if enabled.
        :param tree: the AST of a program.
        :return: None
        """
        if self.config.typecheck != TypeCheckLevel.DISABLED:
            type_checker = TypeCheckVisitor(symbol_table)
            type_checker.visit(tree)
            z3 = Z3Solver()
            self.log.info(type_checker.smt_string)
            if not z3.solve(type_checker.smt_string):
                raise TypeError("The BioScript program could not be safely type checked.")
        else:
            self.log.debug("Type checking has been disabled.")
