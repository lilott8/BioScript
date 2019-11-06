from abc import ABCMeta

from chemicals.identifier import NaiveIdentifier
from compiler.config.compiler_cli import CompilerCLI
from compiler.data_structures.basic_block import BasicBlock
from compiler.data_structures.program import Program
from compiler.data_structures.symbol_table import SymbolTable
from compiler.semantics.header_visitor import HeaderVisitor
from compiler.semantics.ir_visitor import IRVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.symbol_visitor import SymbolTableVisitor
from compiler.passes.transforms.simd_expansion import SIMDExpansion
from compiler.passes.pass_manager import PassManager
from compiler.targets.ir_target import IRTarget
from compiler.targets.mfsim_target import MFSimTarget
from compiler.compiler import BSCompiler


class FrontEndBase(metaclass=ABCMeta):

    @staticmethod
    def run_globals(tree, symbol_table: SymbolTable = SymbolTable()) -> SymbolTable:
        header_visitor = HeaderVisitor(symbol_table, NaiveIdentifier())
        header_visitor.visit(tree)
        return header_visitor.symbol_table

    @staticmethod
    def run_methods(tree, symbol_table: SymbolTable) -> SymbolTable:
        method_visitor = MethodVisitor(symbol_table)
        method_visitor.visit(tree)
        return method_visitor.symbol_table

    @staticmethod
    def run_symbols(tree, symbol_table: SymbolTable) -> SymbolTable:
        symbol_visitor = SymbolTableVisitor(symbol_table, NaiveIdentifier())
        symbol_visitor.visit(tree)
        return symbol_visitor.symbol_table

    @staticmethod
    def run_ir(tree, symbol_table: SymbolTable) -> IRVisitor:
        ir_visitor = IRVisitor(symbol_table)
        ir_visitor.visit(tree)
        return ir_visitor

    def get_symbols(self, tree):
        st = FrontEndBase.run_globals(tree, SymbolTable())
        st = FrontEndBase.run_symbols(tree, st)
        return FrontEndBase.run_methods(tree, st)

    def get_ir(self, tree):
        st = FrontEndBase.run_globals(tree, SymbolTable())
        st = FrontEndBase.run_symbols(tree, st)
        st = FrontEndBase.run_methods(tree, st)
        return FrontEndBase.run_ir(tree, st)

    def get_compiled_ir(self, tree):
        # This resets the basic block counter right before we
        # traverse the IR visitor.  This makes testing for
        # basic block id deterministic and independent of
        # the order in which tests are run.
        BasicBlock.id_counter = 1
        ir = self.get_ir(tree)

        expander = SIMDExpansion()
        target = IRTarget(expander.transform(Program(functions=ir.functions, symbol_table=ir.symbol_table,
                                  bb_graph=ir.graph, name="TEST_FILE", calls=ir.calls,
                                  config=CompilerCLI(["-d", "-t", "ir", "-i", "TEST_FILE"]).config)))
        target.transform()
        return target

    def get_compiled_mfsim(self, tree, file):
        BasicBlock.id_counter = 1
        ir = self.get_ir(tree)
        ir = Program(functions=ir.functions, config=CompilerCLI(["-d", "-t", "mfsim", "-i", file, "-o", "output/"]).config,
                       symbol_table=ir.symbol_table, bb_graph=ir.graph, name=file, calls=ir.calls)
        pm = PassManager(ir)
        pm.run_analysis()
        pm.run_transformations()
        prog = pm.program

        target = MFSimTarget(prog)
        target.transform()
        return str([target.num_cgs, target.num_transfers, target.num_dags, target.num_detects,
                target.num_dispense, target.num_dispose, target.num_edges, target.num_heats,
                target.num_mixes, target.num_splits])
