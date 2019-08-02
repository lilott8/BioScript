from compiler.data_structures.function import Function
from compiler.data_structures.variable import *
from grammar.parsers.python.BSParser import BSParser
from .bs_base_visitor import BSBaseVisitor


class MethodVisitor(BSBaseVisitor):
    """
    This only parses the methods of an input file.
    It does resolve symbols for function definition;
    But nothing more.  It will only resolve typing
    Of a function iff an identifier is provided.
    It cannot resolve typing of a method if an identifier
    Is provided but it's typing has not yet been defined.
    """

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Method Visitor")
        # This holds all the unresolved functions -- functions
        # that return a function.  This is required because
        # if you have a(b(c())), you'll never know what c()
        # or b() return without looking back after they've
        # been constructed.
        self.unresolved = set()

    def visitProgram(self, ctx: BSParser.ProgramContext):
        if ctx.functions():
            self.visitFunctions(ctx.functions())
        pass

    def visitFunctions(self, ctx: BSParser.FunctionsContext):
        for func in ctx.functionDeclaration():
            self.visitFunctionDeclaration(func)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        """
        This populates the symbol table with methods.
        It cannot handle return values.  So all records
        In the symbol table will be empty typed.
        :param ctx: visitor context
        :return: nothing
        """
        name = ctx.IDENTIFIER().__str__()

        self.symbol_table.new_scope(name)
        types = set()

        if ctx.functionTyping():
            types = self.visitFunctionTyping(ctx.functionTyping())

        args = list()
        if ctx.formalParameters():
            args = self.visitFormalParameters(ctx.formalParameters())

        return_var = self.visitReturnStatement(ctx.returnStatement())
        if not return_var:
            self.unresolved.add(name)

        bs_function = Function(name, types, args, return_var=return_var)

        self.symbol_table.functions[name] = bs_function
        self.symbol_table.end_scope()

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        if ctx.primary():
            ret = self.visitPrimary(ctx.primary())
        else:
            ret = self.visitMethodCall(ctx.methodCall())

        # Because primary can emit a literal, we have to look
        # at all variables.  As literals are global.
        ret_var = self.symbol_table.get_variable(ret['name'])

        return ret_var

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

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        function = self.symbol_table.functions[ctx.IDENTIFIER().__str__()]

        return function
