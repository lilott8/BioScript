import copy

from bioscript.visitors.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import UndefinedException
from shared.enums.chemtypes import ChemTypeResolver
from shared.enums.chemtypes import ChemTypes
from shared.enums.config_flags import TypeChecker
from shared.variable import Variable


class TypeCheckVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        # We deep copy symbol table because we don't
        # want to affect change on the created one.
        super().__init__(copy.deepcopy(symbol_table))
        self.check = self.config.typecheck
        self.smt_string = ""
        self.build_declares()
        self.output = None

    def get_smt_name(self, var: Variable, chemtype: ChemTypes = None) -> str:
        string = "{}_{}".format(BSBaseVisitor.get_safe_name(var.scope), BSBaseVisitor.get_safe_name(var.name))
        if chemtype:
            string += "_{}".format(chemtype.name)
        return string

    def add_smt(self, smt: str):
        self.smt_string += "{}{}".format(smt, self.nl)

    def build_declares(self):
        if self.check == TypeChecker.UNION:
            types = ChemTypeResolver.available_types
        else:
            types = ChemTypeResolver.naive_types
            types.add(ChemTypes.UNKNOWN)

        declares = ""
        mats = ""
        for name, var in self.symbol_table.globals.items():
            declares += "; Declaring constants for: {}{}".format(self.get_smt_name(var), self.nl)
            for enum in types:
                declares += "(declare-const {} Bool){}".format(self.get_smt_name(var, ChemTypes(enum)), self.nl)
        for name, scope in self.symbol_table.scope_map.items():
            for symbol in scope.locals:
                var = scope.locals[symbol]
                declares += "; Declaring constants for: {}{}".format(self.get_smt_name(var), self.nl)
                for enum in types:
                    declares += "(declare-const {} Bool){}".format(self.get_smt_name(var, ChemTypes(enum)), self.nl)
                if not var.types - ChemTypeResolver.numbers:
                    mats += "; {} is a mat{}".format(self.get_smt_name(var), self.nl)
                    mats += "(assert {}{}(not{}{}{}(or{}{}{}{}(= {} true)" \
                            "{}{}{}{}(= {} true){}{}{}){}{}){}){}".format(self.nl, self.tab, self.nl,
                                                                          self.tab, self.tab, self.nl,
                                                                          self.tab, self.tab, self.tab,
                                                                          self.get_smt_name(var,
                                                                                            ChemTypes.REAL),
                                                                          self.nl, self.tab, self.tab,
                                                                          self.tab,
                                                                          self.get_smt_name(var,
                                                                                            ChemTypes.NAT),
                                                                          self.nl,
                                                                          self.tab, self.tab, self.nl,
                                                                          self.tab, self.nl, self.nl)
        self.add_smt(declares)
        self.add_smt(mats)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        for func in ctx.functionDeclaration():
            self.visitFunctionDeclaration(func)

        for statement in ctx.statements():
            self.visitStatements(statement)

        self.add_smt("(check-sat)")

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        return super().visitManifestDeclaration(ctx)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        return super().visitStationaryDeclaration(ctx)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]

        self.scope_stack.append(name)

        for statement in ctx.statements():
            self.visitStatements(statement)

        self.scope_stack.pop()
        return ""

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

    def visitAssignmentOperations(self, ctx: BSParser.AssignmentOperationsContext):
        ret = {"op": ''}
        if ctx.mix():
            ret['op'] = 'mix'
            self.visitMix(ctx.mix())
        elif ctx.detect():
            ret['op'] = 'detect'
            ret.update(self.visitDetect(ctx.detect()))
        elif ctx.expression():
            ret['op'] = 'expression'
            temp = self.visitExpression(ctx.expression())
            if temp:
                ret.update(temp)
        elif ctx.split():
            ret['op'] = 'split'
            ret.update(self.visitSplit(ctx.split()))
        elif ctx.methodCall():
            ret['op'] = 'function'
            ret.update(self.visitMethodCall(ctx.methodCall()))
        else:
            self.log.fatal("No operation: {}".format(ctx.getText()))
            return ""
        return ret

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return super().visitStatements(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        return super().visitIfStatement(ctx)

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        return super().visitWhileStatement(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return super().visitRepeat(ctx)

    def visitMix(self, ctx: BSParser.MixContext) -> dict:
        inputs = {'variable': list()}
        x = 0
        for volume in ctx.volumeIdentifier():
            inputs['variable'].append(self.visit(volume)['variable'])
            x += 1

        output = ""
        kill_switch = False
        for input1 in inputs['variable'][0].types:
            for input2 in inputs['variable'][1].types:
                if not self.combiner.epa_manager.validate(input1, input2):
                    kill_switch = True
                output += self.generate_mix_smt(self.output, inputs['variable'][0], inputs['variable'][1], input1,
                                                input2)
        return inputs

    def visitDetect(self, ctx: BSParser.DetectContext) -> dict:
        module = self.symbol_table.get_variable(ctx.IDENTIFIER(0).__str__(), self.scope_stack[-1])
        material = self.symbol_table.get_variable(ctx.IDENTIFIER(1).__str__(), self.scope_stack[-1])
        return {"module": module, 'variable': material}

    def visitHeat(self, ctx: BSParser.HeatContext):

        return super().visitHeat(ctx)

    def visitSplit(self, ctx: BSParser.SplitContext) -> dict:
        return {'variable': self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        return super().visitDispense(ctx)

    def visitDispose(self, ctx: BSParser.DisposeContext):
        return super().visitDispose(ctx)

    def visitExpression(self, ctx: BSParser.ExpressionContext) -> dict:
        ret = {'variable': list()}
        if ctx.primary():
            ret['variable'].append(self.visitPrimary(ctx.primary()))
        else:
            temp = self.visitExpression(ctx.expression(0))
            if temp:
                ret['variable'].append(temp)
            temp = None
            temp = self.visitExpression(ctx.expression(1))
            if temp:
                ret['variable'].append(temp)
            pass
        return ret

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return self.visit(ctx.expression())

    def visitMethodCall(self, ctx: BSParser.MethodCallContext) -> dict:
        return {"function": self.symbol_table.functions[ctx.IDENTIFIER().__str__()]}

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        output = list()
        for expr in ctx.expression():
            output.append(self.visitExpression(expr))
        return output

    def visitTypeType(self, ctx: BSParser.TypeTypeContext):
        return super().visitTypeType(ctx)

    def visitUnionType(self, ctx: BSParser.UnionTypeContext):
        return super().visitUnionType(ctx)

    def visitTypesList(self, ctx: BSParser.TypesListContext):
        return super().visitTypesList(ctx)

    def visitVariableDeclaratorId(self, ctx: BSParser.VariableDeclaratorIdContext):
        return super().visitVariableDeclaratorId(ctx)

    def visitVariableDeclarator(self, ctx: BSParser.VariableDeclaratorContext):
        return super().visitVariableDeclarator(ctx)

    def visitVariableInitializer(self, ctx: BSParser.VariableInitializerContext):
        return super().visitVariableInitializer(ctx)

    def visitArrayInitializer(self, ctx: BSParser.ArrayInitializerContext):
        return super().visitArrayInitializer(ctx)

    def visitLocalVariableDeclaration(self, ctx: BSParser.LocalVariableDeclarationContext):
        self.output = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])

        data = self.visit(ctx.assignmentOperations())

        # if data['op'] == 'mix':
        #     self.log.info("mix: {}".format(data))
        # elif data['op'] == 'split':
        #     self.log.info("split: {}".format(data))
        # elif data['op'] == 'detect':
        #     self.log.info("detect: {}".format(data))
        # elif data['op'] == 'function':
        #     self.log.info("function: {}".format(data))
        # elif data['op'] == 'expression':
        #     self.log.info("expression: {}".format(data))

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        if ctx.IDENTIFIER():
            if not self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]):
                raise UndefinedException("Undeclared variable: {}".format(ctx.IDENTIFIER().__str__()))
            return self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
        elif ctx.literal():
            return self.visitLiteral(ctx.literal())
        else:
            return self.visitExpression(ctx.expression())

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        if ctx.INTEGER_LITERAL():
            return Variable('literal', {ChemTypes.NAT}, self.scope_stack[-1])
        elif ctx.BOOL_LITERAL():
            return Variable('literal', {ChemTypes.BOOL}, self.scope_stack[-1])
        elif ctx.FLOAT_LITERAL():
            return Variable('literal', {ChemTypes.REAL}, self.scope_stack[-1])
        else:
            return Variable('literal', {ChemTypes.CONST}, self.scope_stack[-1])

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        return super().visitPrimitiveType(ctx)

    def generate_mix_smt(self, output, var1, var2, t1, t2):
        smt = "; building asserts for mixing {} and {} in {}{}".format(var1.name.upper(),
                                                                       var2.name.upper(),
                                                                       self.scope_stack[-1].upper(), self.nl)
        smt += "(assert {}{}(=>{}{}{}(and{}{}{}{}(= {} true){}{}{}{}(= {} true){}{}{}){}{}{}(and{}" \
            .format(self.nl,
                    self.tab, self.nl,
                    self.tab, self.tab, self.nl,
                    self.tab, self.tab, self.tab, self.get_smt_name(var1, t1), self.nl,
                    self.tab, self.tab, self.tab, self.get_smt_name(var2, t2), self.nl,
                    self.tab, self.tab, self.nl,
                    self.tab, self.tab, self.nl,
                    self.tab, self.tab, self.nl)
        for out_type in self.combiner.combine_types(t1, t2):
            smt += "{}{}{}(= {} true){}".format(self.tab, self.tab, self.tab, self.get_smt_name(output, out_type),
                                                self.nl)
        smt += ("{}{}){}{}){}){}".format(self.tab, self.tab, self.nl, self.tab, self.nl, self.nl))

        self.add_smt(smt)
        return smt
