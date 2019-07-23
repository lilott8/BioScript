from chemicals.chemtypes import *
from chemicals.identifier import Identifier
from compiler.data_structures.ir import IRInstruction
from compiler.data_structures.properties import BSVolume
from compiler.data_structures.variable import Movable, Number
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *
from .bs_base_visitor import BSBaseVisitor


class SymbolTableVisitor(BSBaseVisitor):

    def __init__(self, symbol_table, identifier: Identifier):
        super().__init__(symbol_table, "Symbol Visitor")
        # The identifier to use.
        self.identifier = identifier
        self.rename = False

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
            #if not self.config.supports_functions:
            #    raise InvalidOperation("Target: {} doesn't support function returns.".format(self.config.target.name))
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

        return {'types': types, 'size': 1, 'instruction': IRInstruction.MIX, "name": IRInstruction.MIX.name}

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
        self.symbol_table.update_symbol(material_name, var['types'])
        return {'types': types, 'size': 1, 'instruction': IRInstruction.DETECT, "name": IRInstruction.DETECT.name}

    def visitHeat(self, ctx: BSParser.HeatContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        var = self.identifier.identify(name, types, self.symbol_table.current_scope.name)
        self.symbol_table.update_symbol(name, var['types'])
        return {'types': types, 'size': 1, 'instruction': IRInstruction.HEAT, "name": IRInstruction.HEAT.name}

    def visitSplit(self, ctx: BSParser.SplitContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        size = int(ctx.INTEGER_LITERAL().__str__())
        if not SymbolTableVisitor.isPower(2, size):
            raise InvalidOperation("Split 2^x-ways is supported; split {}-ways is not supported".format(size))
        return {'types': types, 'size': size, 'instruction': IRInstruction.SPLIT, "name": IRInstruction.SPLIT.name}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        name = ctx.IDENTIFIER().__str__()
        if not self.symbol_table.get_global(name):
            raise InvalidOperation('Trying to dispense: "{}" which is not declared in the manifest.'.format(name))
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return {'types': types, 'size': 1,
                'instruction': IRInstruction.DISPENSE, "name": IRInstruction.DISPENSE.name}

    def visitDispose(self, ctx: BSParser.DisposeContext):
        name = ctx.IDENTIFIER().__str__()
        types = {ChemTypes.MAT}
        self.symbol_table.update_symbol(name, types)
        return {'types': types, 'size': 1, 'instruction': IRInstruction.DISPOSE, "name": IRInstruction.DISPOSE.name}

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        return {"types": {ChemTypes.REAL, ChemTypes.NAT}, "size": 1,
                'instruction': IRInstruction.BINARYOP, "name": IRInstruction.BINARYOP.name}

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return super().visitParExpression(ctx)

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        """
        Infers the types from the method call.
        :param ctx:
        :return: Set of ChemType Enums.
        """
        method_name = ctx.IDENTIFIER().__str__()
        # if not self.config.supports_nesting and self.symbol_table.current_scope.name != "main":
        #     raise UnsupportedOperation("%s architecture does not support nested functions" % self.config.target.name)
        # if not self.config.supports_recursion and self.symbol_table.current_scope.name == method_name:
        #     raise UnsupportedOperation("%s architecture does not support recursion" % self.config.target.name)
        if method_name not in self.symbol_table.functions:
            self.log.fatal("Function {} is not defined.".format(method_name))
        return {'types': self.symbol_table.functions[method_name].types, 'size': 1,
                'instruction': IRInstruction.CALL, 'name': method_name}

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

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return self.visitChildren(ctx)

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        name = self.rename_var(ctx.IDENTIFIER().__str__(), True)

        declared_types = set()
        final_types = set()

        if ctx.unionType():
            declared_types = self.visitUnionType(ctx.unionType())

        operation = self.visitVariableDeclaration(ctx.variableDeclaration())

        final_types = final_types.union(declared_types)
        final_types = final_types.union(operation['types'])

        """
        Some necessary preconditions.  This is written
        this way because of the reasons stated above.
        """
        # If we have x[n] = ... and it's not a power of 2, kill it.
        if ctx.INTEGER_LITERAL() and not SymbolTableVisitor.isPower(2, int(ctx.INTEGER_LITERAL().__str__())):
            raise InvalidOperation("All arrays must be 2^x.")
        if ctx.INTEGER_LITERAL():
            size = int(ctx.INTEGER_LITERAL().__str__())
            if size != operation['size']:
                operation['size'] = size
        if operation['instruction'] == IRInstruction.CALL:
            operation['size'] = self.symbol_table.functions[operation['name']].return_size
            if ctx.INTEGER_LITERAL() and int(ctx.INTEGER_LITERAL().__str__()) != operation['size']:
                raise InvalidOperation("Array size doesn't match method return size.")

        # quick hack for int, float, and time.  easily add volume, etc when we have x = literal
        if final_types.issubset(ChemTypeResolver.numbers):  # assigning a numeric type
            if ctx.variableDeclaration().expression():  # expression
                if ctx.variableDeclaration().expression().primary(): # primary [ can be paren, literal, or variable ]
                    if ctx.variableDeclaration().expression().primary().literal():
                        if ctx.stop.type is 34 or ctx.stop.type is 35:  # 35 = integer literal, 36 = float literal
                            num = ctx.stop.text
                            unit = 1
                        elif ctx.stop.type is 36:  # 36 = TIME number
                            num = ctx.stop.text
                            unit = num[-1:]
                            num = num[:-1]
                            if unit is 'ns':
                                unit = 0.000000001
                            elif unit is 'ms':
                                unit = 0.001
                            elif unit is 's':
                                unit = 1
                            elif unit is 'm':
                                unit = 60
                            elif unit is 'h':
                                unit = 3600
                            elif unit is 'd':
                                unit = 86400
                            else:
                                unit = 1
                        else:
                            num = 1
                            unit = 1
                        variable = Number(name, final_types, self.symbol_table.current_scope.name, value=float(num * unit))
                else:
                    variable = Number(name, final_types, self.symbol_table.current_scope.name, value=float(-1))
                    self.log.warn("%s not properly defined in symbol table" % name)
            else:
                variable = Number(name, final_types, self.symbol_table.current_scope.name, value=float(-1))
                self.log.warn("%s not properly defined in symbol table" % name)
        else:
            variable = Movable(name, final_types, self.symbol_table.current_scope.name, operation['size'])
        self.symbol_table.add_local(variable)

        return None

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
        name = self.rename_var(ctx.IDENTIFIER().__str__())
        types = {ChemTypes.MAT}
        quantity = 10.0
        units = BSVolume.MICROLITRE
        if ctx.VOLUME_NUMBER():
            x = self.split_number_from_unit(ctx.VOLUME_NUMBER().__str__())
            units = BSVolume.get_from_string(x['units'])
            quantity = units.normalize(x['quantity'])

        var = self.identifier.identify(name, types, self.symbol_table.current_scope.name)
        variable = Movable(var['name'], var['types'], var['scope'], volume=quantity, units=units)

        variable.volume = quantity
        variable.unit = units
        return variable

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
