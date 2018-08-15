from bioscript.visitors.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.enums.chemtypes import ChemTypeResolver
from shared.enums.chemtypes import ChemTypes
from shared.enums.config_flags import TypeChecker


class TypeCheckVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table)
        self.check = self.config.typecheck
        self.smt_string = ""
        self.build_declares()
        self.identifier = None
        if self.check == TypeChecker.NAIVE:
            pass

    def build_declares(self):
        for scope in self.symbol_table.scope_map:
            for var in self.symbol_table.scope_map[scope].get_locals():
                self.smt_string += "; Declaring constants for: {}\n".format(var)
                for enum in ChemTypeResolver.available_types:
                    self.smt_string += "declare-const {}_{} Bool\n".format(var, ChemTypes(enum).name)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        return super().visitProgram(ctx)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        return super().visitManifestDeclaration(ctx)

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
        return super().visitBlockStatement(ctx)

    def visitAssignmentOperations(self, ctx: BSParser.AssignmentOperationsContext):
        return super().visitAssignmentOperations(ctx)

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return super().visitStatements(ctx)

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

    def visitVariableDeclaratorId(self, ctx: BSParser.VariableDeclaratorIdContext):
        return super().visitVariableDeclaratorId(ctx)

    def visitVariableDeclarator(self, ctx: BSParser.VariableDeclaratorContext):
        return super().visitVariableDeclarator(ctx)

    def visitVariableInitializer(self, ctx: BSParser.VariableInitializerContext):
        return super().visitVariableInitializer(ctx)

    def visitArrayInitializer(self, ctx: BSParser.ArrayInitializerContext):
        return super().visitArrayInitializer(ctx)

    def visitLocalVariableDeclaration(self, ctx: BSParser.LocalVariableDeclarationContext):
        return super().visitLocalVariableDeclaration(ctx)

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        return super().visitPrimary(ctx)

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        return super().visitLiteral(ctx)

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        return super().visitPrimitiveType(ctx)

    def visitVolumeIdentifier(self, ctx: BSParser.VolumeIdentifierContext):
        return super().visitVolumeIdentifier(ctx)

    def visitTimeIdentifier(self, ctx: BSParser.TimeIdentifierContext):
        return super().visitTimeIdentifier(ctx)

    def visitTemperatureIdentifier(self, ctx: BSParser.TemperatureIdentifierContext):
        return super().visitTemperatureIdentifier(ctx)
