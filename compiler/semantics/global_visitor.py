from chemicals.identifier import Identifier
from compiler.data_structures.variable import *
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser


class GlobalVariableVisitor(BSBaseVisitor):

    def __init__(self, symbol_table, identifier: Identifier):
        super().__init__(symbol_table, "Global Visitor", identifier)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.symbol_table.add_global(Symbol(name.__str__(), "global", {ChemTypes.MODULE}))

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.symbol_table.add_global(Symbol(name.__str__(), "global", self.identifier.identify(name.__str__())))

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.symbol_table.add_global(Symbol(name.__str__(), "global", self.identifier.identify(name.__str__())))
