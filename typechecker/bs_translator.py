from antlr4 import *
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from typechecker.visitors.symbol_visitor import SymbolTableVisitor
from typechecker.visitors.type_visitor import TypeCheckVisitor
from typechecker.symbol_table.symbol_table import SymbolTable
from config.config import Config


class BSTranslator(object):

    def __init__(self):
        config = Config.getInstance(None)
        file_stream = FileStream(config.input)
        self.lexer = BSLexer(file_stream)
        stream = CommonTokenStream(self.lexer)
        self.parser = BSParser(stream)
        self.tree = self.parser.program()

        self.symbol_table = SymbolTable()
        # Build the visitors we need to do this
        self.symbol_visitor = SymbolTableVisitor(self.symbol_table)
        self.visit_symbol_table()
        self.type_checker = TypeCheckVisitor(self.symbol_visitor.symbol_table)
        self.visit_type_check()

    def visit_symbol_table(self):
        # Walk the trees.
        self.symbol_visitor.visit(self.tree)

    def visit_type_check(self):
        self.type_checker.visit(self.tree)
