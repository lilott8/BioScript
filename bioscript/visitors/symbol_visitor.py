from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *
from shared.enums.instructions import Instruction
from shared.variable import *
from .bs_base_visitor import BSBaseVisitor


class SymbolTableVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        # Visiting globals is done in global_visitor.

        for func in ctx.functionDeclaration():
            self.visitFunctionDeclaration(func)

        # We set current_scope equal to main for because the statements
        # hereafter are main's statements.
        self.symbol_table.current_scope = self.symbol_table.scope_map["main"]
        for statement in ctx.statements():
            self.visitStatements(statement)

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
        method.return_size = return_data['size']

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
        variable = Variable(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.add_local(variable)
        return variable

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        # This is a pass-thru function.
        return self.visitUnionType(ctx.unionType())

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        if ctx.methodCall():
            return self.visitMethodCall(ctx.methodCall())
        elif ctx.literal():
            return self.visitLiteral(ctx.literal())
        else:
            variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
            return {'types': variable.types, 'size': variable.size}

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
            # self.log.info(variable)
            self.symbol_table.update_symbol_by_var(variable)
            types = types.union(variable.types)

        if not types:
            types.add(ChemTypes.MAT)

        return {'types': types, 'size': 1, 'instruction': Instruction.MIX, "name": Instruction.MIX.name}

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
        return {'types': types, 'size': 1, 'instruction': Instruction.DETECT, "name": Instruction.DETECT.name}

    def visitHeat(self, ctx: BSParser.HeatContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        var = self.identifier.identify(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.update_symbol(name, var.types)
        return {'types': types, 'size': 1, 'instruction': Instruction.HEAT, "name": Instruction.HEAT.name}

    def visitSplit(self, ctx: BSParser.SplitContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        size = int(ctx.INTEGER_LITERAL().__str__())
        if not SymbolTableVisitor.isPower(2, size):
            raise InvalidOperation("Split 2^x-ways is supported; split {}-ways is not supported".format(size))
        return {'types': types, 'size': size, 'instruction': Instruction.SPLIT, "name": Instruction.SPLIT.name}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return {'types': types, 'size': 1, 'instruction': Instruction.DISPENSE, "name": Instruction.DISPENSE.name}

    def visitDispose(self, ctx: BSParser.DisposeContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return {'types': types, 'size': 1, 'instruction': Instruction.DISPOSE, "name": Instruction.DISPOSE.name}

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        return {"types": {ChemTypes.REAL, ChemTypes.NAT}, "size": 1,
                'instruction': Instruction.EXPRESSION, "name": Instruction.EXPRESSION.name}

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
        return {'types': self.symbol_table.functions[method_name].types, 'size': 1,
                'instruction': Instruction.METHOD, 'name': method_name}

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
        """
        This function could be written in a fashion that is much more efficient.
        I intentionally wrote this for readability.  This is complicated and intricate.
        Choosing to optimize for efficiency would have obfuscated the intricate
        And subtle differences in each case; leading to hard to track bugs.
        :param ctx:
        :return:
        """
        declared_types = set()
        final_types = set()

        if ctx.unionType():
            declared_types = self.visitUnionType(ctx.unionType())

        # Obtain the instruction object
        pair = self.visitChildren(ctx)

        final_types = final_types.union(declared_types)
        final_types = final_types.union(pair['types'])

        variable = None
        id_len = len(ctx.IDENTIFIER())

        """
        Some necessary preconditions.  This is written
        this way because of the reasons stated above.
        """
        # If the id1, id2,..idn is not a power of 2, kill it.
        if not SymbolTableVisitor.isPower(2, id_len):
            raise InvalidOperation("Split 2^x-ways is supported; split {}-ways is not supported".format(pair['size']))
        # If we have x[n] = ... and it's not a power of 2, kill it.
        if ctx.INTEGER_LITERAL() and not SymbolTableVisitor.isPower(2, int(ctx.INTEGER_LITERAL().__str__())):
            raise InvalidOperation("All arrays must be 2^x.")
        if pair['instruction'] == Instruction.METHOD:
            pair['size'] = self.symbol_table.functions[pair['name']].return_size
            if ctx.INTEGER_LITERAL() and int(ctx.INTEGER_LITERAL().__str__()) != pair['size']:
                raise InvalidOperation("Array size doesn't match method return size.")

        """
        If it's a method and there is an integer literal and literal != return
        """

        """
        There are 5 Cases:
        1) id1, id2,... idn = split x into n
        2) id[] = split x into n
        3) id[n] = split | dispense | methodCall by n
        4) id = split
        5) id = !split
        """
        if id_len > 1:
            self.log.warning("We have an id bigger than 1")
            """"
            Case 1: id1, id2,.. idn = split x into n
            Things to check for:
                - We need to iterate ctx.IDENTIFIERS to create all ids
                - We need to check and see if id_len = n
            """
            for count in range(0, len(ctx.IDENTIFIER())):
                name = ctx.IDENTIFIER(count).__str__()
                variable = Variable(name, pair['types'], self.symbol_table.current_scope.name, 1)
                self.symbol_table.add_local(variable)
        elif pair['instruction'] == Instruction.SPLIT and ctx.LBRACKET():
            """
            Case 2: id[] = split x into n
            Case 3: id[n] = split x into n
            Things to check for:
                - n = n
            """
            if ctx.INTEGER_LITERAL():
                count = int(ctx.INTEGER_LITERAL().__str__())
            else:
                count = pair['size']
            variable = Variable(ctx.IDENTIFIER(0).__str__(), pair['types'], self.symbol_table.current_scope.name, count)
            self.symbol_table.add_local(variable)
        elif pair['instruction'] != Instruction.SPLIT and ctx.LBRACKET():
            """
            Case 3: id[n] = mix | dispense | methodCall(), etc.
            Things to check for:
                - Does the method call return an array?
                - Assume id[n] = dispense is a n-ary dispense
            """
            if pair['instruction'] == Instruction.MIX:
                raise InvalidOperation("Individual array index access is not permitted.")
            name = ctx.IDENTIFIER(0).__str__()
            variable = Variable(name, pair['types'],
                                self.symbol_table.current_scope.name, int(ctx.INTEGER_LITERAL().__str__()))
            self.symbol_table.add_local(variable)
        elif pair['instruction'] == Instruction.SPLIT and not ctx.LBRACKET():
            """
            Case 4: id = split x into n
            Things to check for:
                - nothing to note.
            """
            name = ctx.IDENTIFIER(0).__str__()
            variable = Variable(name, pair['types'], self.symbol_table.current_scope.name, pair['size'])
            self.symbol_table.add_local(variable)
        else:
            """
            Case 5: id = !split
            """
            name = ctx.IDENTIFIER(0).__str__()
            variable = Variable(name, pair['types'], self.symbol_table.current_scope.name, pair['size'])
            self.symbol_table.add_local(variable)

        return variable

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        return super().visitPrimary(ctx)

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        return {'types': {ChemTypes.NAT}, 'size': 1}

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

    @staticmethod
    def isPower(x, y):
        """
        Determines if y is a power of x
        :param x: base
        :param y: exponent
        :return: true if input == x^y
        """
        if x == 1:
            return y == 1
        power = 1
        while power < y:
            power = power * x

        return power == y
