from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser


class MFSimVisitor(TargetVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "MFSimVisitor")
        self.open = "{"
        self.close = "}"

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        self.add("")
        self.add("{")
        self.add('"EXPERIMENT": {')
        self.add('{}"NAME": "{}",'.format(self.tab, self.config.input_file))
        self.add('"INPUTS": [')

        self.add(self.visitManifestDeclaration(ctx.manifestDeclaration()))
        self.add(self.visitStationaryDeclaration(ctx.stationaryDeclaration()))
        self.add(self.visitModuleDeclaration(ctx.moduleDeclaration()))

        self.add('],{}'.format(self.nl))

        self.add('"INSTRUCTIONS": [')
        for statement in ctx.statements():
            # self.add(self.visitStatements(statement))
            pass
        self.add('],')

        self.add("}")
        return super().visitProgram(ctx)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        output = ""

        return output

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        output = "{{{}".format(self.nl)
        for manifest in ctx.IDENTIFIER():
            output += '"VARIABLE_DECLARATION": {{{}'.format(self.nl)
            output += '"ID": "{}",{}'.format(manifest.__str__(), self.nl)
            output += '"NAME": "{}",{}'.format(manifest.__str__(), self.nl)
            output += '"TYPE": "CHEMICAL"{}'.format(self.nl)
            output += "}}{}}},".format(self.nl)

        return output[:-1]

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        output = '{ "VARIABLE_DECLARATION": {'

        return output + "}}{}}},".format(self.nl)

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
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        return super().visitIfStatement(ctx)

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        return super().visitWhileStatement(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return super().visitRepeat(ctx)

    def visitMix(self, ctx: BSParser.MixContext):
        return super().visitMix(ctx)

    def visitDetect(self, ctx: BSParser.DetectContext):
        return super().visitDetect(ctx)

    def visitHeat(self, ctx: BSParser.HeatContext):
        return super().visitHeat(ctx)

    def visitSplit(self, ctx: BSParser.SplitContext):
        return super().visitSplit(ctx)

    def visitDispense(self, ctx: BSParser.DispenseContext):
        return super().visitDispense(ctx)

    def visitDispose(self, ctx: BSParser.DisposeContext):
        return super().visitDispose(ctx)

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        return super().visitExpression(ctx)

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

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        return super().visitPrimary(ctx)

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        return super().visitLiteral(ctx)

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        return super().visitPrimitiveType(ctx)
