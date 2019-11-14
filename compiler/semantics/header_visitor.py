from chemicals.identifier import Identifier
from compiler.data_structures.function import Function
from compiler.data_structures.variable import *
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import UndefinedFunction


class HeaderVisitor(BSBaseVisitor):

    def __init__(self, symbol_table, identifier: Identifier):
        super().__init__(symbol_table, "Global Visitor", identifier)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        for header in ctx.globalDeclarations():
            self.visitGlobalDeclarations(header)
        if ctx.functions():
            self.visitFunctions(ctx.functions())

    def visitGlobalDeclarations(self, ctx: BSParser.GlobalDeclarationsContext):
        return super().visitGlobalDeclarations(ctx)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        self.symbol_table.add_global(Symbol(ctx.IDENTIFIER().__str__(), self.symbol_table.global_scope,
                                            {ChemTypes.MODULE}))

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        symbol = Symbol(ctx.IDENTIFIER().__str__(), self.symbol_table.global_scope, set())
        if ctx.unionType():
            symbol.types.update(self.visitUnionType(ctx.unionType()))
        symbol.types.update(self.identifier.identify(symbol.name, symbol.types))
        self.symbol_table.add_global(symbol)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        symbol = Symbol(ctx.IDENTIFIER().__str__(), self.symbol_table.global_scope, set())
        if ctx.unionType():
            symbol.types.update(self.visitUnionType(ctx.unionType()))
        symbol.types.update(self.identifier.identify(symbol.name, symbol.types))
        self.symbol_table.add_global(symbol)

    def visitFunctions(self, ctx: BSParser.FunctionsContext):
        for func in ctx.functionDeclaration():
            self.visitFunctionDeclaration(func)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        """
        This populates the symbol table with methods.
        It does not visit statements.
        :param ctx: visitor context
        :return: nothing
        """
        name = ctx.IDENTIFIER().__str__()

        self.symbol_table.new_scope(name)
        types = {ChemTypes.UNKNOWN}

        if ctx.functionTyping():
            types = self.visitFunctionTyping(ctx.functionTyping())

        args = list()
        if ctx.formalParameters():
            temp_args = self.visitFormalParameters(ctx.formalParameters())
            args = list()
            for arg in temp_args:
                self.symbol_table.add_local(Symbol(arg['name'], name, arg['types']))
                args.append(arg['name'])

        bs_function = Function(name, types, args)

        if name in self.symbol_table.functions.keys():
            raise UndefinedFunction("Trying to redeclare function: {}.".format(name))

        self.symbol_table.functions[name] = bs_function
        self.symbol_table.end_scope()

    def visitFormalParameters(self, ctx: BSParser.FormalParametersContext):
        if ctx.formalParameterList():
            return self.visitFormalParameterList(ctx.formalParameterList())
        else:
            return list()

    def visitFormalParameterList(self, ctx: BSParser.FormalParameterListContext):
        args = list()
        for param in ctx.formalParameter():
            args.append(self.visitFormalParameter(param))
        return args

    def visitFormalParameter(self, ctx: BSParser.FormalParameterContext):
        types = set()
        if ctx.unionType():
            types = self.visitUnionType(ctx.unionType())
        else:
            types.add(ChemTypes.UNKNOWN)

        name = ctx.IDENTIFIER().__str__()
        return {'name': name, 'types': types}

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        # This is a pass-thru function.
        return self.visitUnionType(ctx.unionType())
