import colorlog
from antlr4 import *

from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.symbol_visitor import SymbolTableVisitor
from bioscript.visitors.targets.clang_visitor import ClangVisitor
from bioscript.visitors.targets.target_factory import TargetFactory
from bioscript.visitors.type_visitor import TypeCheckVisitor
from config.config import Config
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from shared.enums.config_flags import TypeChecker


class BSTranslator(object):

    def __init__(self):
        self.config = Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.warning(self.config.input)
        self.type_check = ""
        self.typeable = False
        # This must be globally declared.
        self.symbol_visitor = SymbolTableVisitor(SymbolTable())

    def translate(self):
        file_stream = FileStream(self.config.input)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        tree = parser.program()

        # No matter what options are set,
        # We must visit the symbol table.
        self.symbol_visitor.visit(tree)

        if self.config.typecheck != TypeChecker.DISABLED:
            self.visit_type_check(tree)
        else:
            self.typeable = True

        if not self.typeable:
            raise TypeError("The BioScript program could not be safely type checked.")
            return

        # if self.config.llvm:
        #     self.visit_clang(tree)
        #     self.log.info("Run LLVM here")
        # else:
        #     self.log.info("You're not running LLVM")

        self.log.info(self.config.target)
        target = TargetFactory.get_target(self.config.target, self.symbol_visitor.symbol_table)
        self.log.info("Visiting: {}".format(target.name))
        target.visit(tree)
        self.log.debug(self.symbol_visitor.symbol_table)
        # target.print_program()

    def visit_type_check(self, tree):
        type_checker = TypeCheckVisitor(self.symbol_visitor.symbol_table)
        type_checker.visit(tree)
        # self.log.info(type_checker.smt_string)
        # z3 = Z3Solver()
        # if z3.solve(type_checker.smt_string):
        #     self.typeable = True

    def visit_clang(self, tree):
        clang = ClangVisitor(self.symbol_visitor.symbol_table)
        clang.visit(tree)
        # self.log.info(clang.program)
