from timeit import default_timer as timer

import colorlog
from antlr4 import *

import compiler.config.config as config
from compiler.data_structures.program import Program
from compiler.data_structures.symbol_table import SymbolTable
from compiler.data_structures.writable import Writable, WritableType
from compiler.passes.pass_manager import PassManager
from compiler.semantics.header_visitor import HeaderVisitor
from compiler.semantics.ir_visitor import IRVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.symbol_visitor import SymbolTableVisitor
from compiler.semantics.type_visitor import TypeCheckVisitor
from compiler.targets.target_selector import TargetSelector
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from solvers.z3_solver import Z3Solver


class BSCompiler(object):

    def __init__(self, configuration: config.Config):
        self.config = configuration
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.log.warning(self.config.input)
        # The symbol table is built in phases,
        # And used in many place, hence it's globalness.
        self.symbol_table = None
        # This is the representation of an input program.
        self.program = None

    def compile(self):
        times = {"sa": 0, "opts": 0, "target": 0}

        start = timer()
        ir = self.translate(self.config.input)
        times['sa'] = timer() - start

        start = timer()
        self.log.error("Turning off all optimizations")
        # prog = self.optimizations(self.program)
        times['opts'] = timer() - start

        start = timer()
        target = self.target(ir)
        times['target'] = timer() - start

        times['write'] = 0
        if self.config.write_out:
            start = timer()
            for key, writable in self.program.write.items():
                writable.write()
            times['write'] = timer() - start
        else:
            self.log.warning("Not writing any output to disk.")
            if self.log.debug:
                for key, writable in self.program.write.items():
                    self.log.info('{}: \n{}'.format(key, writable.content))

        if self.config.print_stats:
            stats = "\n"
            stats += "Semantic Analysis:\t{}\n".format(round(times['sa'], 4))
            stats += "Optimizations:\t\t{}\n".format(round(times['opts']), 4)
            stats += "Target Gen:\t\t\t{}\n".format(round(times['target'], 4))
            stats += "Writing to disk:\t{}\n".format(round(times['write'], 4))
            stats += "Total:\t\t\t\t{}".format(round(sum(times.values()), 4))
            self.log.debug(stats)

        if not target:
            self.log.critical("You aren't doing anything with the results of the compile function.")

    def translate(self, filename: str) -> Program:
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

        # We can rely on Python's shallow copy and pass by reference semantics
        # to create only one object and allow all the passes to update it.
        symbol_table = SymbolTable()
        identifier = self.config.identify.get_identifier()

        visitor_passes = [HeaderVisitor(symbol_table, identifier), SymbolTableVisitor(symbol_table, identifier),
                          MethodVisitor(symbol_table)]

        if self.config.typecheck:
            visitor_passes.append(TypeCheckVisitor(symbol_table, self.config.combine.get_combiner(
                self.config.epa_defs, self.config.abstract_interaction), self.config.types_used))

        visitor_passes.append(IRVisitor(symbol_table))

        for visitor in visitor_passes:
            if self.config.debug:
                self.log.info("Running {} pass.".format(visitor.visitor_name))
            visitor.visit(tree)

        ir = visitor_passes[-1]
        self.program = Program(functions=ir.functions, config=self.config,
                               symbol_table=ir.symbol_table, bb_graph=ir.graph,
                               name=self.config.input_file, calls=ir.calls)

        if self.config.write_cfg:
            for root in self.program.functions:
                self.program.write['{}_basic_block_graph'.format(root)] = Writable(self.program.name,
                                                                                   "{}/{}_{}_basic_blocks.dot".format(
                                                                                       self.config.output,
                                                                                       self.program.name, root),
                                                                                   self.program.functions[root][
                                                                                       'graph'], WritableType.GRAPH)
        return self.program

    def optimizations(self, program: Program):
        """
        Run the various optimizations that can be run.
        :param program:
        :return:
        """
        passes = PassManager(self.program)
        passes.run_analysis()
        passes.run_transformations()
        # return passes
        return passes.program

    def target(self, program: Program):
        """
        Run the various transforms that can be run.
        :param program:
        :return:
        """
        target = None
        if self.config.target != TargetSelector.DISABLED:
            target = self.config.target.get_target(program)
            self.log.info("Running {} transform.".format(self.config.target.name))
            target.transform()
        return target

    def visit_type_check(self, tree, symbol_table: SymbolTable):
        """
        Attempts to typecheck a program if enabled.
        :param tree: the AST of a program.
        :param symbol_table: The symbol table of the program.
        :return: None
        """
        if self.config.typecheck:
            combiner = self.config.combine.get_combiner(self.config.epa_defs, self.config.abstract_interaction)
            type_checker = TypeCheckVisitor(symbol_table, combiner, self.config.types_used)
            type_checker.visit(tree)
            z3 = Z3Solver()
            self.log.info(type_checker.smt_string)
            if not z3.solve(type_checker.smt_string):
                raise TypeError("The BioScript program could not be safely type checked.")
        else:
            self.log.debug("Type checking has been disabled.")
