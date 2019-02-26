import colorlog
from antlr4 import *

from compiler.data_structures.bs_program import BSProgram
from compiler.data_structures.symbol_table import SymbolTable
from compiler.semantics.global_visitor import GlobalVariableVisitor
from compiler.semantics.ir_visitor import IRVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.phi_inserter import PhiInserter
from compiler.semantics.symbol_visitor import SymbolTableVisitor
from compiler.semantics.type_visitor import TypeCheckVisitor
from compiler.targets.target_manager import TargetManager
from config.config import Config
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from shared.enums.config_flags import TypeChecker
from solvers.z3_solver import Z3Solver


class BSCompiler(object):

    def __init__(self):
        self.config = Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.warning(self.config.input)
        # The symbol is built is phases, hence it's globalness.
        self.symbol_table = None
        self.program = BSProgram()

    def compile(self):
        self.program.name = self.config.input
        ir = self.translate(self.config.input)
        ir = self.optimizations(self.program)
        target = self.target(self.program)

    def translate(self, filename: str) -> dict:
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
        # Always update the symbol table.
        self.program.symbol_table = global_visitor.symbol_table

        # Build the functions and their symbols next.
        method_visitor = MethodVisitor(self.program.symbol_table)
        method_visitor.visit(tree)
        # Always update the symbol table.
        self.program.symbol_table = method_visitor.symbol_table

        # Finish building the symbol table.
        symbol_visitor = SymbolTableVisitor(method_visitor.symbol_table)
        symbol_visitor.visit(tree)
        # Always update the symbol table.
        self.program.symbol_table = symbol_visitor.symbol_table

        # Attempt to type check the program
        self.visit_type_check(tree)

        # Convert the AST to the IR for further analysis.
        ir_visitor = IRVisitor(self.program.symbol_table)
        ir_visitor.visit(tree)
        # Always update the symbol table.
        self.program.symbol_table = ir_visitor.symbol_table

        phi = PhiInserter(self.program.symbol_table, ir_visitor.get_ir())
        phi.insert_phi_nodes()

        return ir_visitor.get_ir()

    def optimizations(self, program: BSProgram):
        """
        Run the various optimizations that can be run.
        :param program:
        :return:
        """
        # passes = PassManager(self.symbol_table, ir)
        # passes.optimize()
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

    def visit_type_check(self, tree):
        """
        Attempts to typecheck a program if enabled.
        :param tree: the AST of a program.
        :return: None
        """
        if self.config.typecheck != TypeChecker.DISABLED:
            type_checker = TypeCheckVisitor(self.symbol_table)
            type_checker.visit(tree)
            z3 = Z3Solver()
            if not z3.solve(type_checker.smt_string):
                raise TypeError("The BioScript program could not be safely type checked.")
        else:
            self.log.debug("Type checking has been disabled.")
