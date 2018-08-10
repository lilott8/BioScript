from antlr4 import *
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from bioscript.visitors.symbol_visitor import SymbolTableVisitor
from bioscript.visitors.type_visitor import TypeCheckVisitor
from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.clang_visitor import ClangVisitor
from config.config import Config
import colorlog


class BSTranslator(object):

    def __init__(self):
        self.config = Config.getInstance(None)
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.warning(self.config.input)

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

        self.visit_type_check(tree)
        self.visit_clang(tree)

    def visit_type_check(self, tree):
        type_checker = TypeCheckVisitor(self.symbol_visitor.symbol_table)
        type_checker.visit(tree)

    def visit_clang(self, tree):
        clang = ClangVisitor(self.symbol_visitor.symbol_table)
        clang.visit(tree)
