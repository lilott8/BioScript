from grammar.parsers.python.BSParser import BSParser
from shared.enums.chemtypes import ChemTypes
from shared.function import Function
from shared.variable import Variable
from .bs_base_visitor import BSBaseVisitor


class SymbolTableVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        for func in ctx.functionDeclaration():
            self.visitFunctionDeclaration(func)

        for statement in ctx.statements():
            self.visitStatements(statement)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        types = {ChemTypes.MODULE}
        for name in ctx.IDENTIFIER():
            variable = self.identifier.identify(name.__str__(), types=types, scope=self.global_scope)
            self.symbol_table.add_global(variable)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        types = {ChemTypes.MAT}
        for name in ctx.IDENTIFIER():
            variable = self.identifier.identify(name.__str__(), types=types, scope=self.global_scope)
            self.symbol_table.add_global(variable)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        types = {ChemTypes.MAT}
        for name in ctx.IDENTIFIER():
            variable = self.identifier.identify(name.__str__(), types=types, scope=self.global_scope)
            self.symbol_table.add_global(variable)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()

        self.symbol_table.add_new_scope(name)
        types = set()

        if ctx.functionTyping():
            types = self.visitFunctionTyping(ctx.functionTyping())

        args = list()
        if ctx.formalParameters():
            args = self.visitFormalParameters(ctx.formalParameters())
        for arg in args:
            self.symbol_table.add_local(arg)

        for statement in ctx.statements():
            self.visitStatements(statement)

        return_name = self.visitReturnStatement(ctx.returnStatement())
        types = types.union(self.symbol_table.get_variable(return_name).types)

        bs_function = Function(name, types, args)
        self.symbol_table.add_function(bs_function)

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
        variable = Variable(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.add_local(variable)
        return variable

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        # This is a pass-thru function.
        return self.visitUnionType(ctx.unionType())

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return ctx.IDENTIFIER().__str__()

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        return super().visitBlockStatement(ctx)

    def visitAssignmentOperations(self, ctx: BSParser.AssignmentOperationsContext):
        return self.visitChildren(ctx)

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        return super().visitIfStatement(ctx)

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        return super().visitWhileStatement(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return super().visitRepeat(ctx)

    def visitMix(self, ctx: BSParser.MixContext):
        types = set()
        for fluid in ctx.volumeIdentifier():
            variable = self.visitVolumeIdentifier(fluid)
            self.symbol_table.update_symbol_by_var(variable)
            types = types.union(variable.types)

        if not types:
            types.add(ChemTypes.MAT)

        return types

    def visitDetect(self, ctx: BSParser.DetectContext):
        types = {ChemTypes.REAL}
        module_name = ctx.IDENTIFIER(0).__str__()
        material_name = ctx.IDENTIFIER(1).__str__()

        if not self.symbol_table.get_global(module_name):
            self.log.fatal("Undefined Module: {}".format(module_name))

        if not self.symbol_table.get_variable(material_name):
            self.log.fatal("Undefined Variable: {}".format(material_name))
        material_types = {ChemTypes.MAT}
        var = self.identifier.identify(material_name, material_types, self.symbol_table.current_scope.name)
        self.symbol_table.update_symbol(material_name, var.types)
        return types

    def visitHeat(self, ctx: BSParser.HeatContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        var = self.identifier.identify(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.update_symbol(name, var.types)
        return types

    def visitSplit(self, ctx: BSParser.SplitContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return types

    def visitDispense(self, ctx: BSParser.DispenseContext):
        self.log.fatal("Dispense is not correct.  It is missing an IDENTIFIER().")
        name = ""
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return types

    def visitDispose(self, ctx: BSParser.DisposeContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return types

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        return {ChemTypes.REAL, ChemTypes.NAT}

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return super().visitParExpression(ctx)

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        """
        Infers the types from the method call.
        :param ctx:
        :return: Set of ChemType Enums.
        """
        method_name = ctx.IDENTIFIER().__str__()
        if method_name not in self.symbol_table.functions:
            self.log.fatal("Function {} is not defined.".format(method_name))
        return self.symbol_table.functions[method_name].types

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        return self.visitChildren(ctx)

    def visitTypeType(self, ctx: BSParser.TypeTypeContext):
        # A simple pass-thru function.
        return self.visitPrimitiveType(ctx.primitiveType())

    def visitUnionType(self, ctx: BSParser.UnionTypeContext):
        # A simple pass-thru function.
        return self.visitTypesList(ctx.typesList())

    def visitTypesList(self, ctx: BSParser.TypesListContext):
        """
        Grab all the defined types.
        :param ctx:
        :return: set of ChemType Enums
        """
        types = set()
        for t in ctx.typeType():
            types.add(self.visitTypeType(t))
        return types

    def visitArrayInitializer(self, ctx: BSParser.ArrayInitializerContext):
        return int(ctx.INTEGER_LITERAL())

    def visitLocalVariableDeclaration(self, ctx: BSParser.LocalVariableDeclarationContext):
        """
        x = some assignment statement
        :param ctx:
        :return: Variable
        """
        inferred_types = set()
        declared_types = set()
        final_types = set()

        name = ctx.IDENTIFIER().__str__()

        if ctx.unionType():
            declared_types = self.visitUnionType(ctx.unionType())

        inferred_types = self.visitChildren(ctx)

        final_types = final_types.union(declared_types)
        final_types = final_types.union(inferred_types)

        variable = Variable(name, final_types, self.symbol_table.current_scope.name)

        if ctx.arrayInitializer():
            variable.is_array = True


        self.symbol_table.add_local(variable)
        return variable

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        return super().visitPrimary(ctx)

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        return super().visitLiteral(ctx)

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        """
        Get the primitive type from the input.
        :param ctx:
        :return: ChemType Enum
        """
        if ctx.MAT():
            return ChemTypes.MAT
        elif ctx.BOOL():
            return ChemTypes.BOOL
        elif ctx.NAT:
            return ChemTypes.NAT
        elif ctx.REAL():
            return ChemTypes.REAL
        else:
            self.log.warning("A custom type has been discovered.")
            return ChemTypes.UNKNOWN

    def visitVolumeIdentifier(self, ctx: BSParser.VolumeIdentifierContext):
        """
        Get the variable name from the input.
        :param ctx:
        :return: Variable
        """
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        return self.identifier.identify(name, types, self.symbol_table.current_scope.name)

    def visitTimeIdentifier(self, ctx: BSParser.TimeIdentifierContext):
        return super().visitTimeIdentifier(ctx)

    def visitTemperatureIdentifier(self, ctx: BSParser.TemperatureIdentifierContext):
        return super().visitTemperatureIdentifier(ctx)

