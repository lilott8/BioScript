from grammar.parsers.python.BSParser import BSParser
from grammar.parsers.python.BSParserVisitor import BSParserVisitor
import colorlog
from config.log_config import bslog
from shared.enums.bs_properties import BSTime, BSTemperature, BSVolume
from shared.enums.chemtypes import ChemTypes
import re


class ClangVisitor(BSParserVisitor):

    def __init__(self, symbol_table):
        BSParserVisitor.__init__(self)
        self.symbol_table = symbol_table
        self.log = bslog.getLogger(self.__class__.__name__)
        self.nl = "\n"
        self.program = "// BSProgram!" + self.nl
        self.program += "#include <unistd.h>" + self.nl + "#include <random>" + self.nl
        self.program += self.build_structs()
        self.program += self.build_functions()

    def add(self, input):
        self.program += input + self.nl

    def print_program(self):
        self.log.warning(self.program)
        pass

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        for function in ctx.functionDeclaration():
            self.visitFunctionDeclaration(function)

        self.add("int main {")

        for statement in ctx.statements():
            self.visitStatements(statement)

        self.add("}")

        #return super().visitProgram(ctx)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.add("module " + name.__str__() + ";")

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.add("mat " + name.__str__() + ";")
        pass

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        for name in ctx.IDENTIFIER():
            self.add("mat " + name.__str__() + ";")
        pass

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]

        if ChemTypes.MAT in func.types:
            output = "mat "
        else:
            output = "double "

        output += "{} (".format(name)
        if func.args:
            for arg in func.args:
                output += "{}, ".format(arg.name)
            output = output[:-2]
        output += ") {{{}".format(self.nl)

        for statement in ctx.statements():
            self.visitStatements(statement)

        output += "return {};{}".format(self.visitReturnStatement(ctx.returnStatement()), self.nl)
        output += "}} {}".format(self.nl)

        self.add(output)

    def visitFormalParameters(self, ctx: BSParser.FormalParametersContext):
        return super().visitFormalParameters(ctx)

    def visitFormalParameterList(self, ctx: BSParser.FormalParameterListContext):
        return super().visitFormalParameterList(ctx)

    def visitFormalParameter(self, ctx: BSParser.FormalParameterContext):
        return super().visitFormalParameter(ctx)

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        return super().visitFunctionTyping(ctx)

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return ctx.IDENTIFIER().__str__()

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
        name = ctx.IDENTIFIER()
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())
        output = "{} = heat({}, {}, {});".format(name, name, temp['quantity'], time['quantity'])
        self.add(output)

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
        return ctx.IDENTIFIER().__str__()

    def visitVariableDeclarator(self, ctx: BSParser.VariableDeclaratorContext):
        return self.visitChildren(ctx)

    def visitVariableInitializer(self, ctx: BSParser.VariableInitializerContext):
        return self.visitChildren(ctx)

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
        quantity = 10
        units = BSVolume.MICROLITRE
        if ctx.VOLUME_NUMBER():
            x = self.split_number_from_unit(ctx.VOLUME_NUMBER().__str__())
            units = BSVolume.get_from_string(x['units'])
            quantity = units.normalize(x['quantity'])
        return {'quantity': quantity, 'units': units,
                'variable': self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())}

    def visitTimeIdentifier(self, ctx: BSParser.TimeIdentifierContext):
        x = self.split_number_from_unit(ctx.TIME_NUMBER().__str__())
        # self.log.info(x)
        units = BSTime.get_from_string(x['units'])
        self.log.error(type(units))
        quantity = units.normalize(x['quantity'])
        self.log.error(quantity)
        return {'quantity': quantity, 'units': units}

    def visitTemperatureIdentifier(self, ctx: BSParser.TemperatureIdentifierContext):
        x = self.split_number_from_unit(ctx.TEMP_NUMBER().__str__())
        units = BSTemperature.get_from_string(x['units'])
        self.log.error(units)
        quantity = units.normalize(x['quantity'])
        return {'quantity': quantity, 'units': units}

    def split_number_from_unit(self, text):
        temp_float = ""
        temp_unit = ""
        for x in text[0:]:
            if str.isdigit(x):
                temp_float += x
            elif x == ".":
                temp_float += x
            elif x == ",":
                continue
            else:
                temp_unit += x

        self.log.info("{} {}".format(temp_float, temp_unit))
        return {'quantity': float(temp_float), 'units': temp_unit}

    def build_structs(self):
        output = "struct mat {double quantity;};" + self.nl
        output += "struct splitMat{mat values[100];};" + self.nl
        output += "struct module{int x, y;};" + self.nl

        return output

    def build_functions(self):
        output = "mat mix(mat input1, mat input2, double quantity) {" + self.nl
        output += "mat output;" + self.nl
        output += "output.quantity = input1.quantity + input2.quantity;" + self.nl
        output += "sleep(quantity);" + self.nl
        output += "return output;" + self.nl
        output += "}" + self.nl

        output += "splitMat split(mat input, int quantity) {" + self.nl
        output += "splitMat output;" + self.nl
        output += "for (int x =0; x < quantity; x++) {" + self.nl
        output += "output.values[x] = input;" + self.nl
        output += "output.values[x].quantity = input.quantity/(float)quantity;" + self.nl
        output += "}" + self.nl
        output += "return output;" + self.nl
        output += "}" + self.nl

        output += "mat heat(mat input, double temp, double time) {" + self.nl
        output += "sleep(time);" + self.nl
        output += "return input;" + self.nl
        output += "}" + self.nl

        output += "double detect(mat input, module detect, double quantity) {" + self.nl
        output += "sleep(quantity);" + self.nl
        output += "return -1.0;" + self.nl
        output += "}" + self.nl

        output += "mat dispense(mat input, double quantity) {" + self.nl
        output += "mat output = input;" + self.nl
        output += "output.quantity = quantity;" + self.nl
        output += "return input;" + self.nl
        output += "}" + self.nl

        output += "void dispose(mat input) {" + self.nl
        output += "}" + self.nl

        return output
