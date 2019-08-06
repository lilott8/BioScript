from compiler.data_structures.variable import *
from grammar.parsers.python.BSParser import BSParser
from .bs_base_visitor import BSBaseVisitor


class MethodVisitor(BSBaseVisitor):
    """
    Basically handles the issue of method chaining.
    It will finish building the typing information
    of chained methods and also grab the typing information
    for method invocations.
    """

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Method Visitor")
        # Keeps track of the return-chain of methods.
        # This allows methods to be defined out of order,
        # without typing information, and all be chained together.
        self.call_chain = dict()

    def visitProgram(self, ctx: BSParser.ProgramContext):
        # Visit the functions, for the 3rd time.
        if ctx.functions():
            self.visitFunctions(ctx.functions())

        self.scope_stack.append("main")
        self.symbol_table.current_scope = self.symbol_table.scope_map[self.scope_stack[-1]]
        # While this visits *all* the statements,
        # it only looks at the methodInvocation
        # statements.
        for statement in ctx.statements():
            self.visitStatements(statement)
        self.scope_stack.pop()

        # The last attempt to find the types of a method chain.
        # Because we know the chain, we can simply crawl the chain
        # and the first thing to give us typing information,
        # because it is called from a function, we grab it,
        # and assign it to the unknown function.
        for name, objekt in self.symbol_table.functions.items():
            if not objekt.types:
                types = set()
                find = name
                while not types and find in self.call_chain.keys():
                    types = self.symbol_table.functions[find].types
                    find = self.call_chain[find]
                objekt.types = types


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
        function = self.symbol_table.functions[name]
        self.scope_stack.append(name)

        # If this case arises, then we know
        if ChemTypes.UNKNOWN in function.types and len(function.types) == 1:
            ret = self.visitReturnStatement(ctx.returnStatement())
            # If this is a variable, grab the symbol and make the update.
            # Otherwise it's a function call.
            if 'method' not in ret.keys():
                symbol = self.symbol_table.get_local(ret['name'], name)
                function.types.update(symbol.types)
            else:
                function.types.update(ret['types'])
        function.types.remove(ChemTypes.UNKNOWN)
        self.scope_stack.pop()

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

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        if ctx.methodCall():
            method = self.visitMethodCall(ctx.methodCall())
            self.call_chain[self.scope_stack[-1]] = method['name']
            return self.visitMethodCall(ctx.methodCall())
        else:
            return self.visitPrimary(ctx.primary())

    def visitMethodInvocation(self, ctx: BSParser.MethodInvocationContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        # Get the symbol.
        symbol = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])
        # Grab the function.
        function = self.visitMethodCall(ctx.methodCall())
        # Update the types of the symbol.
        symbol.types.update(function['types'])
        # Save the symbol.
        self.symbol_table.update_symbol(symbol)

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        function = self.symbol_table.functions[ctx.IDENTIFIER().__str__()]
        return {'name': function.name, 'types': function.types, 'method': True}
