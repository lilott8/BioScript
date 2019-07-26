from chemicals.identifier import Identifier
from compiler.data_structures.variable import Movable
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *
from .bs_base_visitor import BSBaseVisitor


class SymbolTableVisitorV2(BSBaseVisitor):

    def __init__(self, symbol_table, identifier: Identifier):
        super().__init__(symbol_table, "Symbol Visitor")
        # The identifier to use.
        self.identifier = identifier
        self.rename = False

    def visitProgram(self, ctx: BSParser.ProgramContext):
        # Visiting globals is done in global_visitor.

        if ctx.functions():
            self.visitChildren(ctx.functions())

        # We set current_scope equal to main for because the statements
        # hereafter are main's statements.
        # self.symbol_table.current = self.symbol_table.local["main"]
        for statement in ctx.statements():
            self.visitStatements(statement)

    def visitFunctions(self, ctx: BSParser.FunctionsContext):
        return super().visitFunctions(ctx)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        return super().visitFunctionDeclaration(ctx)

    def visitFormalParameters(self, ctx: BSParser.FormalParametersContext):
        return super().visitFormalParameters(ctx)

    def visitFormalParameterList(self, ctx: BSParser.FormalParameterListContext):
        return super().visitFormalParameterList(ctx)

    def visitFormalParameter(self, ctx: BSParser.FormalParameterContext):
        return super().visitFormalParameter(ctx)

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        return super().visitFunctionTyping(ctx)

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return super().visitReturnStatement(ctx)

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        return super().visitBlockStatement(ctx)

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return super().visitStatements(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        return super().visitIfStatement(ctx)

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        return super().visitWhileStatement(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return super().visitRepeat(ctx)

    def visitHeat(self, ctx: BSParser.HeatContext):
        return super().visitHeat(ctx)

    def visitDispose(self, ctx: BSParser.DisposeContext):
        return super().visitDispose(ctx)

    def visitMix(self, ctx: BSParser.MixContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())

        uses = list()
        for fluid in ctx.variable():
            temp = self.visitVariable(fluid)
            uses.append({"var": self.symbol_table.get_local(temp['name']), "index": temp['index']})

        deff['index'] = 0 if uses[0]['index'] != -1 and uses[1]['index'] != -1 else deff['index']

        # If it is -1 we use the size of the variable, because we are
        # issuing a SIMD instruction.  Otherwise, we just grab the
        # index and run with it.
        use_a = uses[0]['var'].size if uses[0]['index'] == -1 else 1
        use_b = uses[1]['var'].size if uses[1]['index'] == -1 else 1

        # Verify the operation consumes equal amounts of variable(s)
        if use_a != use_b:
            self.log.fatal("Tyring to mix variables of unequal size.")
            raise UnsupportedOperation("Tyring to mix variables of unequal size.")

        # Build the types of this new variable.
        types = set(uses[0]['var'].types)
        types.union(uses[1]['var'].types)

        # We arbitrarily pick a size, because they should be the same.
        variable = Movable(deff['name'], types, self.symbol_table.current_scope.name, size=use_a)

        # These are the intermediate containers for notifying
        # the variable's value property things have changed.
        volumes = {'op': 'mix', 'values': dict()}
        expire_a = {'op': 'use', 'values': dict()}
        expire_b = {'op': 'use', 'values': dict()}
        if use_a == 1:
            # This exists, because the operation could be x[n] = mix a[m] with b[k]
            # And we have to make sure the index of x is maintained through the op.
            # We need to add the volumes of the first and second inputs into one object.
            volumes['values'][deff['index']] = {
                "input_1": {"quantity": uses[0]['var'].value[uses[0]['index']].volume['quantity'],
                            'units': uses[0]['var'].value[uses[0]['index']].volume['units']},
                "input_2": {"quantity": uses[1]['var'].value[uses[1]['index']].volume['quantity'],
                            'units': uses[1]['var'].value[uses[1]['index']].volume['units']}}
            # We need to remove the volume from the first mix input.
            expire_a['values'][uses[0]['index']] = {
                'quantity': uses[0]['var'].value[uses[0]['index']].volume['quantity'],
                'units': uses[0]['var'].value[uses[0]['index']].volume['units']}
            # We need to remove the volume from the second mix input.
            expire_b['values'][uses[1]['index']] = {
                'quantity': uses[1]['var'].value[uses[1]['index']].volume['quantity'],
                'units': uses[1]['var'].value[uses[1]['index']].volume['units']}
        else:
            for x in range(use_a):
                # Add the volumes of the first and second inputs into one object.
                volumes['values'][x] = {"input_1": {"quantity": uses[0]['var'].value[x].volume['quantity'],
                                                    'units': uses[0]['var'].value[x].volume['units']},
                                        "input_2": {"quantity": uses[1]['var'].value[x].volume['quantity'],
                                                    'units': uses[1]['var'].value[x].volume['units']}}
                # Remove the volume from the first mix input.
                expire_a['values'][x] = {'quantity': uses[0]['var'].value[x].volume['quantity'],
                                         'units': uses[0]['var'].value[x].volume['units']}
                # Remove the volume from the second mix input.
                expire_b['values'][x] = {'quantity': uses[1]['var'].value[x].volume['quantity'],
                                         'units': uses[1]['var'].value[x].volume['units']}

        # Set the variable's value property's to reflect the changes.
        variable.value = volumes
        uses[0]['var'].value = expire_a
        uses[1]['var'].value = expire_b

        # Add the new variable to the symbol table.
        self.symbol_table.add_local(variable)
        return None

    def visitDetect(self, ctx: BSParser.DetectContext):
        return super().visitDetect(ctx)

    def visitSplit(self, ctx: BSParser.SplitContext):
        return super().visitSplit(ctx)

    def visitDispense(self, ctx: BSParser.DispenseContext):
        var = self.visitVariableDefinition(ctx.variableDefinition())

        if not self.symbol_table.get_global(ctx.IDENTIFIER().__str__()):
            self.log.fatal("{} isn't declared in the manifest".format(ctx.IDENTIFIER().__str__()))
            raise UndefinedException("{} isn't declared in the manifest".format(ctx.IDENTIFIER().__str__()))

        variable = Movable(var['name'], self.symbol_table.get_global(ctx.IDENTIFIER().__str__()).types,
                           self.symbol_table.current_scope.name, size=var['index'], volume=10.0)

        self.symbol_table.add_local(variable)

    def visitGradient(self, ctx: BSParser.GradientContext):
        return super().visitGradient(ctx)

    def visitStore(self, ctx: BSParser.StoreContext):
        return super().visitStore(ctx)

    def visitMath(self, ctx: BSParser.MathContext):
        return super().visitMath(ctx)

    def visitBinops(self, ctx: BSParser.BinopsContext):
        return super().visitBinops(ctx)

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return super().visitParExpression(ctx)

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        return super().visitMethodCall(ctx)

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        return super().visitExpressionList(ctx)

    def visitTypeType(self, ctx: BSParser.TypeTypeContext):
        return super().visitTypeType(ctx)

    def visitUnionType(self, ctx: BSParser.UnionTypeContext):
        return super().visitUnionType(ctx)

    def visitTypesList(self, ctx: BSParser.TypesListContext):
        return super().visitTypesList(ctx)

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        return super().visitVariableDefinition(ctx)

    def visitVariable(self, ctx: BSParser.VariableContext):
        return super().visitVariable(ctx)

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        return super().visitPrimitiveType(ctx)

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
