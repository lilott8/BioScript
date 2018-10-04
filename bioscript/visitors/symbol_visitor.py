from grammar.parsers.python.BSParser import BSParser
from shared.variable import *
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

        # We set current_scope equal to main for because the statements
        # hereafter are main's statements.
        self.symbol_table.current_scope = self.symbol_table.scope_map["main"]
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

        self.scope_stack.append(name)
        # This sets the current scope.  At this point,
        # The scope should have been created by now.
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]
        method = self.symbol_table.functions[name]
        types = set()

        for statement in ctx.statements():
            self.visitStatements(statement)

        return_data = self.visitReturnStatement(ctx.returnStatement())
        method.types = types.union(return_data['types'])

        self.symbol_table.functions[name] = method

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
        self.log.info(name)
        variable = Variable(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.add_local(variable)
        return variable

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        # This is a pass-thru function.
        return self.visitUnionType(ctx.unionType())

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        if ctx.methodCall():
            return self.visitMethodCall(ctx.methodCall())
        else:
            return {'types': self.symbol_table.get_variable(ctx.IDENTIFIER().__str__()).types, 'size': 1}

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        return super().visitBlockStatement(ctx)

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

        return {'types': types, 'size': 1}

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
        return {'types': types, 'size': 1}

    def visitHeat(self, ctx: BSParser.HeatContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        var = self.identifier.identify(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.update_symbol(name, var.types)
        return {'types': types, 'size': 1}

    def visitSplit(self, ctx: BSParser.SplitContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        size = int(ctx.INTEGER_LITERAL().__str__())
        return {'types': types, 'size': size}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return {'types': types, 'size': 1}

    def visitDispose(self, ctx: BSParser.DisposeContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return {'types': types, 'size': 1}

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        return {"types": {ChemTypes.REAL, ChemTypes.NAT}, "size": 1}

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
        return {'types': self.symbol_table.functions[method_name].types, 'size': 1}

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

    def visitMaterialAssignmentOperations(self, ctx: BSParser.MaterialAssignmentOperationsContext):
        return self.visitChildren(ctx)

    def visitNumericAssignmentOperations(self, ctx: BSParser.NumericAssignmentOperationsContext):
        return self.visitChildren(ctx)

    def visitNumericDeclaration(self, ctx: BSParser.NumericDeclarationContext):
        types = set()

        name = ctx.IDENTIFIER().__str__()

        if ctx.unionType():
            types = self.visitUnionType(ctx.unionType())

        pair = self.visitNumericAssignmentOperations(ctx.numericAssignmentOperations())
        types = types.union(pair['types'])

        variable = Variable(name, types, self.symbol_table.current_scope.name, pair['size'])
        self.symbol_table.add_local(variable)

        return variable

    def visitMaterialDeclaration(self, ctx: BSParser.MaterialDeclarationContext):
        declared_types = set()
        final_types = set()

        name = ctx.IDENTIFIER().__str__()

        if ctx.unionType():
            declared_types = self.visitUnionType(ctx.unionType())

        pair = self.visitChildren(ctx)

        final_types = final_types.union(declared_types)
        final_types = final_types.union(pair['types'])

        variable = Variable(name, final_types, self.symbol_table.current_scope.name, pair['size'])
        self.symbol_table.add_local(variable)

        return variable

    # def visitLocalVariableDeclaration(self, ctx: BSParser.LocalVariableDeclarationContext):
    #     """
    #     x = some assignment statement
    #     :param ctx:
    #     :return: Variable
    #     """
    #     inferred_types = set()
    #     declared_types = set()
    #     final_types = set()
    #
    #     name = ctx.IDENTIFIER().__str__()
    #
    #     if ctx.unionType():
    #         declared_types = self.visitUnionType(ctx.unionType())
    #
    #     inferred_types = self.visitChildren(ctx)
    #
    #     final_types = final_types.union(declared_types)
    #     final_types = final_types.union(inferred_types)
    #
    #     if not ctx.LBRACKET():
    #         variable = Scalar(name, final_types, self.symbol_table.current_scope.name)
    #     else:
    #         if ctx.INTEGER_LITERAL():
    #             size = int(ctx.INTEGER_LITERAL().__str__())
    #         else:
    #             size = -1
    #         variable = Array(name, final_types, self.symbol_table.current_scope.name, size)
    #
    #     self.symbol_table.add_local(variable)
    #     return variable

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

