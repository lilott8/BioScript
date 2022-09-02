from chemicals.identifier import Identifier
from compiler.data_structures.function import Function
from compiler.data_structures.variable import *
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import UndefinedFunction
from antlr4 import *
from grammar.parsers.python.BSLexer import BSLexer

import os


class HeaderVisitor(BSBaseVisitor):

    def __init__(self, symbol_table, identifier: Identifier):
        super().__init__(symbol_table, "Global Visitor", identifier)
        # we simply copy all statements in the tree for each function def
        self.imported = set()

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

    def import_compiled_function(self, filename, prefix=""):
        name = prefix+filename.split('/')[-1].split('.')[0]

        self.symbol_table.new_scope(name)
        types = {ChemTypes.UNKNOWN}
        args = list()

        # parse out arg names
        with open(filename, "r") as file:
            for line in file.readlines():
                if line.__contains__("PARAM("):
                    arg = {'name': line.split(',')[-1].strip()[:-1], 'types': {ChemTypes.UNKNOWN}}
                    self.symbol_table.add_local(Symbol(arg['name'], name, arg['types']))
                    args.append(arg['name'])

        bs_function = Function(name, types, args)

        # we're ok with redefinition, when important.  'namespaced' functions can be imported directly with
        #   import lib.func (used as lib.func())
        #       or
        #   import lib   (use any function in lib, i.e., lib.foo())
        if name in self.symbol_table.functions.keys():
            self.log.warning(f'Redefining function "{name}" during import.')
            pass

        self.symbol_table.functions[name] = bs_function
        self.symbol_table.end_scope()

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext, prefix=""):
        """
        This populates the symbol table with methods.
        It does not visit statements.
        :param ctx: visitor context
        :param prefix: for library function calls, we provide library name
        :return: nothing
        """
        name = prefix+ctx.IDENTIFIER().__str__()

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
            if name in self.imported:
                # TODO -- verify #/type params before allowing override for those imported from .bs files
                #  we can redefine functions that were imported, but overriding should only be allowed
                #  (based on #/type params) when functions are explicitly defined in the .bs file.
                self.imported.remove(name)
            else:  # redeclaring within this file
                raise UndefinedFunction("Trying to redeclare function: {}.".format(name))

        self.symbol_table.functions[name] = bs_function
        self.symbol_table.end_scope()
        # self.functions[name] = ctx.statements()
        # self.functions[name].append(ctx.returnStatement())

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
