from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.enums.instructions import Instruction


class PuddleVisitor(TargetVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "PuddleVisitor")
        self.tab_count = 0
        self.tab = "\t"

    def increment_tab(self):
        self.tab += "\t"
        self.tab_count += 1

    def decrement_tab(self):
        self.tab = ""
        self.tab_count -= 1

        if self.tab_count < 0:
            self.tab_count = 0

        for x in range(0, self.tab_count):
            self.tab += "\t"

    def visitProgram(self, ctx: BSParser.ProgramContext):
        output = "from puddle import mk_session, project_path"

        output += 'arch_path = project_path("{}"){}'.format('PUT SOMETHING HERE', self.nl)
        output += 'with mk_session(arh_path) as session:{}'.format(self.nl)

        output += "{}{}".format(self.tab, self.visitManifestDeclaration(ctx.manifestDeclaration()))

        for i in ctx.statements():
            output += self.visitStatements(i)

        self.compiled = self.nl + output

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        output = ""
        self.log.fatal(
            "Start by adding https://github.com/uwmisl/puddle/blob/master/src/python/examples/thermocycle.py")
        raise Exception
        # for manifest in ctx.MANIFEST():
        #     name = manifest.__str__()
        #     output += '{} = session.input("{}", volume=1000000.0, dimensions=('.format(1,2,)
        # return output

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        return super().visitStationaryDeclaration(ctx)

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
        output = ""
        for x in ctx.statements():
            output += "{}{}{}".format(self.tab, self.visitStatements(x), self.nl)
        return output

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        output = ""
        # Build the if condition....
        condition = self.visitParExpression(ctx.parExpression())
        output += "{}if {}:{}".format(self.tab, condition, self.nl)
        # Increment the tab
        self.increment_tab()
        # Visit the statements
        output += self.visitBlockStatement(ctx.blockStatement(0))
        self.decrement_tab()

        if ctx.ELSE():
            output += "{}else:{}".format(self.tab, self.nl)
            self.increment_tab()
            output += self.visitBlockStatement(ctx.blockStatement(1))
            self.decrement_tab()

        return output

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        output = ""

        condition = self.visitParExpression(ctx.parExpression())
        output += "{}while {}:{}".format(self.tab, condition, self.nl)
        self.increment_tab()
        output += self.visitBlockStatement(ctx.blockStatement())
        self.decrement_tab()

        return output

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        output = ""

        value = int(ctx.INTEGER_LITERAL().__str__())
        output += "{}while {}>0:{}".format(self.tab, value, self.nl)
        self.increment_tab()
        output += self.visitBlockStatement(ctx.blockStatement())
        self.decrement_tab()

        return output

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

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "({})".format(self.visitExpression(ctx.expression()))

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        return super().visitMethodCall(ctx)

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        return super().visitExpressionList(ctx)

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> dict:
        pass

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> dict:
        pass
