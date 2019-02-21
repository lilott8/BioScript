import colorlog
import networkx as nx
from antlr4 import *
from networkx.drawing.nx_pydot import write_dot

# from compiler.visitors import ClangVisitor
from compiler.semantics.global_visitor import GlobalVariableVisitor
from compiler.semantics.ir_visitor import IRVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.symbol_visitor import SymbolTableVisitor
from compiler.semantics.symbol_visitor_v2 import SymbolVisitorV2
# from bioscript.visitors import TargetVisitor
from compiler.semantics.type_visitor import TypeCheckVisitor
from compiler.symbol_table import SymbolTable
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

        # rename_visitor = RenameVisitor(self.global_visitor.symbol_table)
        # No matter what options are set,
        # We must visit the symbol table.
        self.symbol_visitor = SymbolTableVisitor(method_visitor.symbol_table)
        self.symbol_visitor.visit(tree)

        v2 = SymbolVisitorV2(method_visitor.symbol_table)
        v2.visit(tree)
        self.log.info(v2.basic_blocks)

        if self.config.typecheck != TypeChecker.DISABLED:
            self.visit_type_check(tree)
        else:
            self.typeable = True

        if not self.typeable:
            raise TypeError("The BioScript program could not be safely type checked.")

        # target = TargetFactory.get_target(self.config.target, self.symbol_visitor.symbol_table)
        # self.log.info("Visiting: {}".format(target.name))

        ir_visitor = IRVisitor(self.symbol_visitor.symbol_table)
        ir_visitor.visit(tree)
        # self.log.info(ir_visitor.globals)
        # self.log.info(ir_visitor.basic_blocks)
        pos = nx.nx_agraph.graphviz_layout(v2.graph)
        nx.draw(v2.graph, pos=pos)
        write_dot(v2.graph, 'file.dot')

        # target.visit(tree)

        if self.config.debug:
            # target.print_program()
            pass
        if self.config.llvm:
            # self.compile_file(target)
            pass

    def visit_type_check(self, tree):
        type_checker = TypeCheckVisitor(self.symbol_visitor.symbol_table)
        type_checker.visit(tree)
        # self.log.info(type_checker.smt_string)
        # z3 = Z3Solver()
        # if z3.solve(type_checker.smt_string):
        #     self.typeable = True

    def visit_clang(self, tree):
        # clang = ClangVisitor(self.symbol_visitor.symbol_table)
        # clang.visit(tree)
        # self.log.info(clang.program)
        pass

    # def compile_file(self, target: TargetVisitor):
    #     file_name = self.config.path + 'compiled/{}.cpp'.format(self.config.input_file)
    #     f = open(file_name, 'w+')
    #     f.write(target.compiled)
    #     f.close()
    #     subprocess.call(['g++', '-S', '-emit-llvm', file_name])
