from abc import ABCMeta

from chemicals.identifier import NaiveIdentifier
from compiler.data_structures.program import Program
from compiler.data_structures.symbol_table import SymbolTable
from compiler.semantics.header_visitor import HeaderVisitor
from compiler.semantics.ir_visitor import IRVisitor
from compiler.semantics.method_visitor import MethodVisitor
from compiler.semantics.symbol_visitor import SymbolTableVisitor


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
        st = FrontEndBase.run_methods(tree, st)
        st = FrontEndBase.run_symbols(tree, st)
        return FrontEndBase.run_ir(tree, st)

    def get_program(self, tree):
        ir = self.get_ir(tree)
        return Program(functions=ir.functions, globalz=ir.globalz,
                       symbol_table=ir.symbol_table, bb_graph=ir.graph,
                       name="TEST_FILE", calls=ir.calls)
