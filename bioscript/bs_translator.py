import subprocess

import colorlog
from antlr4 import *

from bioscript.symbol_table.symbol_table import SymbolTable
from bioscript.visitors.global_visitor import GlobalVariableVisitor
from bioscript.visitors.method_visitor import MethodVisitor
from bioscript.visitors.symbol_visitor import SymbolTableVisitor
from bioscript.visitors.targets.clang_visitor import ClangVisitor
from bioscript.visitors.targets.target_factory import TargetFactory
from bioscript.visitors.targets.target_visitor import TargetVisitor
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
        # This gets run first, gathering all the globals.
        self.global_visitor = GlobalVariableVisitor(SymbolTable())
        # This must be globally declared.
        self.symbol_visitor = None

    def translate(self):
        file_stream = FileStream(self.config.input)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        tree = parser.program()

        self.global_visitor.visit(tree)
        method_visitor = MethodVisitor(self.global_visitor.symbol_table)
        method_visitor.visit(tree)
        # No matter what options are set,
        # We must visit the symbol table.
        self.symbol_visitor = SymbolTableVisitor(method_visitor.symbol_table)
        self.symbol_visitor.visit(tree)

        # self.log.info(self.symbol_visitor.symbol_table)

        if self.config.typecheck != TypeChecker.DISABLED:
            self.visit_type_check(tree)
        else:
            self.typeable = True

        if not self.typeable:
            raise TypeError("The BioScript program could not be safely type checked.")

        target = TargetFactory.get_target(self.config.target, self.symbol_visitor.symbol_table)
        self.log.info("Visiting: {}".format(target.name))
        target.visit(tree)
        if self.config.debug:
            target.print_program()
            pass
        if self.config.llvm:
            self.compile_file(target)

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

    def compile_file(self, target: TargetVisitor):
        file_name = self.config.path + 'compiled/{}.cpp'.format(self.config.input_file)
        f = open(file_name, 'w+')
        f.write(target.compiled)
        f.close()
        subprocess.call(['g++', '-S', '-emit-llvm', file_name])
