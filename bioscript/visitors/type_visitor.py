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
        self.expressions = list()

    def get_smt_name(self, var: Variable, chemtype: ChemTypes = None) -> str:
        string = "{}_{}".format(BSBaseVisitor.get_safe_name(var.scope), BSBaseVisitor.get_safe_name(var.name))
        if chemtype:
            string += "_{}".format(chemtype.name)
        return string

    def add_smt(self, smt: str):
        self.smt_string += "{}{}".format(smt, self.nl)

    def kill_switch(self):
        kill = ";===================={};KILL SWITCH{};===================={}".format(self.nl, self.nl, self.nl)
        kill += "(assert (= true false)){}".format(self.nl)
        return kill

    def build_declares(self):
        if self.check == TypeChecker.UNION:
            types = ChemTypeResolver.available_types
        else:
            types = ChemTypeResolver.naive_types
            types.add(ChemTypes.UNKNOWN)

        declares = ""
        defines = ""
        asserts = ""

        for name, var in self.symbol_table.globals.items():
            """
            Declare the constants for all global variables.
            """
            declares += "; Declaring constants for: {}{}".format(self.get_smt_name(var).upper(), self.nl)
            for enum in types:
                declares += "(declare-const {} Bool){}".format(self.get_smt_name(var, ChemTypes(enum)), self.nl)
            declares += self.nl
            defines += "; Defining the assignment of: {}{}".format(self.get_smt_name(var).upper(), self.nl)
            for t in var.types:
                """
                Now we actually state the typing assignment of each variable.
                """
                defines += "(assert (= {} true)){}".format(self.get_smt_name(var, t), self.nl)

            if self.config.typecheck == TypeChecker.NAIVE:
                """
                If it's naive, then make sure that unknown is false.
                In other words, we must have a nat/real/mat type.
                """
                defines += "; Ensure that {} is a not unknown type{}".format(self.get_smt_name(var).upper(), self.nl)
                defines += "(assert (= {} false)){}".format(self.get_smt_name(var, ChemTypes.UNKNOWN), self.nl)
        for name, scope in self.symbol_table.scope_map.items():
            """
            Declare the constants for all local variables.
            """
            for symbol in scope.locals:
                var = scope.locals[symbol]
                declares += "; Declaring constants for: {}{}".format(self.get_smt_name(var).upper(), self.nl)
                for enum in types:
                    """
                    Declare the constants for all scoped variables.
                    """
                    declares += "(declare-const {} Bool){}".format(self.get_smt_name(var, ChemTypes(enum)), self.nl)

                declares += self.nl
                defines += "; Defining the assignment of: {}{}".format(self.get_smt_name(var).upper(), self.nl)
                for t in var.types:
                    defines += "(assert (= {} true)){}".format(self.get_smt_name(var, t), self.nl)

                if self.config.typecheck == TypeChecker.NAIVE:
                    """
                    If it's naive, then make sure that unknown is false.
                    In other words, we must have a nat/real/mat type.
                    """
                    defines += "; Ensure that {} is not unknown type{}".format(self.get_smt_name(var).upper(), self.nl)
                    defines += "(assert (= {} false)){}".format(self.get_smt_name(var, ChemTypes.UNKNOWN), self.nl)
                if var.types & ChemTypeResolver.numbers:
                    """
                    Build the asserts for things that are numbers.
                    We will only check naively: in that if we intersect,
                    And we have something, then we know it's a number.
                    """
                    asserts += self.assert_material(var, False)
                if var.types & ChemTypeResolver.materials:
                    """
                    Build the asserts for things that are numbers.
                    We will only check naively: in that if we intersect,
                    And we have something, then we know it's a mat.
                    """
                    asserts += self.assert_material(var)
        self.add_smt("; ==============={}; Declaring Constants{}; ==============={}".format(self.nl, self.nl, self.nl))
        self.add_smt(declares)
        # self.add_smt("; ==============={}; Declaring typing{}; ==============={}".format(self.nl, self.nl, self.nl))
        # self.add_smt(defines)
        self.add_smt("; ==============={}; Declaring Asserts{}; ==============={}".format(self.nl, self.nl, self.nl))
        self.add_smt(asserts)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        smt = ""

        for func in ctx.functionDeclaration():
            smt += self.visitFunctionDeclaration(func)

        for statement in ctx.statements():
            smt += self.visitStatements(statement)

        smt += "(check-sat)"
        self.add_smt(smt)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        return super().visitManifestDeclaration(ctx)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        return super().visitStationaryDeclaration(ctx)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]

        smt = ""

        self.scope_stack.append(name)

        for statement in ctx.statements():
            smt += self.visitStatements(statement)

        self.scope_stack.pop()
        return smt

    def visitFormalParameters(self, ctx: BSParser.FormalParametersContext):
        return super().visitFormalParameters(ctx)

    def visitFormalParameterList(self, ctx: BSParser.FormalParameterListContext):
        return super().visitFormalParameterList(ctx)

    def visitFormalParameter(self, ctx: BSParser.FormalParameterContext):
        return super().visitFormalParameter(ctx)

    def visitFunctionTyping(self, ctx: BSParser.FunctionTypingContext):
        return super().visitFunctionTyping(ctx)

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return ""

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        return super().visitBlockStatement(ctx)

    # def visitAssignmentOperations(self, ctx: BSParser.AssignmentOperationsContext):
    #     smt = ""
    #     if ctx.mix():
    #         smt = self.visitMix(ctx.mix())
    #     elif ctx.detect():
    #         smt = self.visitDetect(ctx.detect())
    #     elif ctx.expression():
    #         self.expressions = list()
    #         smt = self.visitExpression(ctx.expression())
    #     elif ctx.split():
    #         smt = self.visitSplit(ctx.split())
    #     elif ctx.methodCall():
    #         smt = self.visitMethodCall(ctx.methodCall())
    #     else:
    #         self.log.fatal("No operation: {}".format(ctx.getText()))
    #         return ""
    #     return smt

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return self.visitChildren(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        return self.visitChildren(ctx)

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        return self.visitChildren(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        return self.visitChildren(ctx)

    def visitMix(self, ctx: BSParser.MixContext) -> str:
        smt = ""

        vars = list()

        for volume in ctx.volumeIdentifier():
            vars.append(self.visit(volume)['variable'])

        for var1 in vars:
            for var2 in vars:
                if var1 == var2:
                    continue
                smt = "; building asserts for mixing {} and {} in {}{}".format(var1.name.upper(),
                                                                               var2.name.upper(),
                                                                               self.scope_stack[-1].upper(),
                                                                               self.nl)
                for t1 in var1.types:
                    for t2 in var2.types:
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
                            smt += "{}{}{}(= {} true){}".format(self.tab, self.tab, self.tab,
                                                                self.get_smt_name(self.output, out_type),
                                                                self.nl)
                        smt += "{}{}){}{}){})".format(self.tab, self.tab, self.nl, self.tab, self.nl)

        return smt

    def visitDetect(self, ctx: BSParser.DetectContext) -> str:
        module = self.symbol_table.get_variable(ctx.IDENTIFIER(0).__str__(), self.scope_stack[-1])
        material = self.symbol_table.get_variable(ctx.IDENTIFIER(1).__str__(), self.scope_stack[-1])

        smt = "; building asserts for detect {} in {}{}".format(material.name.upper(),
                                                                self.scope_stack[-1].upper(), self.nl)
        smt += "(assert (or (= {} true)(= {} true))){}".format(self.get_smt_name(self.output, ChemTypes.NAT),
                                                               self.get_smt_name(self.output, ChemTypes.REAL), self.nl)
        smt += self.assert_material(material)
        smt += "; building asserts for module {} in {}{}".format(module.name.upper(), "global", self.nl)
        smt += "(assert (= {} true))".format(self.get_smt_name(module, ChemTypes.MODULE))

        return smt

    def visitHeat(self, ctx: BSParser.HeatContext) -> str:
        var = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
        smt = "; building asserts for heat{} in {}{}".format(var.name.upper(), self.scope_stack[-1], self.nl)
        smt += self.assert_material(var)
        return smt

    def visitSplit(self, ctx: BSParser.SplitContext) -> str:
        var = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])

        smt = "; building asserts for split {} in {}{}".format(var.name.upper(),
                                                               self.scope_stack[-1].upper(), self.nl)
        for t in var.types:
            smt += "(assert (= {} true))".format(self.get_smt_name(self.output, t), self.nl)

        return smt

    def visitDispense(self, ctx: BSParser.DispenseContext) -> str:
        smt = "; Not doing any work in dispense{}".format(self.nl)
        return smt

    def visitDispose(self, ctx: BSParser.DisposeContext) -> str:
        smt = "; Not doing any work in dispose{}".format(self.nl)
        return smt

    def visitExpression(self, ctx: BSParser.ExpressionContext) -> str:
        smt = ""
        if ctx.primary():
            smt += self.visitPrimary(ctx.primary())
        else:
            for expr in ctx.expression():
                smt += self.visitExpression(expr)
        return smt

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return self.visit(ctx.expression())

    def visitMethodCall(self, ctx: BSParser.MethodCallContext) -> str:
        func = self.symbol_table.functions[ctx.IDENTIFIER().__str__()]

        smt = "; building asserts for method call {} in {}{}".format(self.output.name.upper(),
                                                                     self.scope_stack[-1].upper(), self.nl)
        for t in func.types:
            smt += "(assert (= {} true)){}".format(self.get_smt_name(self.output, t), self.nl)
        return smt

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

    # def visitLocalVariableDeclaration(self, ctx: BSParser.LocalVariableDeclarationContext):
    #     self.output = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
    #     return self.visit(ctx.assignmentOperations())

    def visitPrimary(self, ctx: BSParser.PrimaryContext) -> str:
        ret = ""
        if ctx.IDENTIFIER():
            if not self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]):
                raise UndefinedException("Undeclared variable: {}".format(ctx.IDENTIFIER().__str__()))
            else:
                var = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
                ret += "; building asserts for expression {} in {}{}".format(var.name.upper(),
                                                                             self.scope_stack[-1].upper(), self.nl)
                ret += self.assert_material(var, False)
        elif ctx.literal():
            ret += ""
        else:
            ret += self.visitExpression(ctx.expression())
        return ret

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

    def assert_material(self, var: Variable, is_mat: bool = True) -> str:
        mats = "; {} is ".format(self.get_smt_name(var))
        knot1 = knot2 = ""

        if is_mat:
            mats += "a MAT{}".format(self.nl)
            knot1 = "{}(not{}".format(self.tab, self.nl)
            knot2 = "{}{}){}".format(self.tab, self.tab, self.nl)
        else:
            mats += "a NAT/REAL{}".format(self.nl)

        mats += "(assert{}".format(self.nl)
        if is_mat:
            mats += knot1
        mats += "(or{}{}{}(= {} true)".format(self.tab, self.tab, self.tab, self.get_smt_name(var, ChemTypes.REAL))
        mats += "{}{}{}(= {} true)".format(self.nl, self.tab, self.tab, self.get_smt_name(var, ChemTypes.NAT))
        if is_mat:
            mats += knot2
        mats += "{}{}){})".format(self.tab, self.tab, self.nl)
        return mats
