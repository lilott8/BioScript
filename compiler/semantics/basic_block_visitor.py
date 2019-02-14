from compiler.data_structures.basic_block import BasicBlock
from compiler.registers import *
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser


class BasicBlockVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        self.basic_blocks = list()
        self.current_block = BasicBlock(1)
        self.register_map = dict()

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        if ctx.functionDeclaration():
            for func in ctx.functionDeclaration():
                # Add the chain of basic blocks resulting from the functions.
                # output += "{}{}{}".format(self.visitFunctionDeclaration(func), self.nl, self.nl)
                pass

        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

        # Add all the subsequent instructions to the B.B.
        for i in ctx.statements():
            self.visitStatements(i)
        self.basic_blocks.append(self.current_block)

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        for module in ctx.IDENTIFIER():
            name = module.__str__()
            self.register_map[name] = Module(self.symbol_table.get_global(name))

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        for manifest in ctx.IDENTIFIER():
            name = manifest.__str__()
            self.register_map[name] = Global(self.symbol_table.get_global(name))

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        for stationary in ctx.IDENTIFIER():
            name = stationary.__str__()
            self.register_map[name] = Stationary(self.symbol_table.get_global(name))

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]

        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]

        for statement in ctx.statements():
            self.visitStatements(statement)

        self.current_block.add(self.visitReturnStatement(ctx.returnStatement()))

        self.scope_stack.pop()
        return None

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        # ir = Return()
        # ir.consumes = self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
        return None

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        # ir = Conditional()
        # ir.condition = self.visitParExpression(ctx.parExpression())
        #
        # self.current_block.add(ir)
        # self.basic_blocks.append(self.current_block)
        # self.current_block = BasicBlock()
        #
        # self.visitBlockStatement(ctx.blockStatement(0))
        #
        # if ctx.ELSE():
        #     self.basic_blocks.append(self.current_block)
        #     self.current_block = BasicBlock()
        #     # Basic Block id it jumps to.
        #     ir.jumps = -1
        #     self.visitBlockStatement(ctx.blockStatement(1))
        #     self.basic_blocks.append(self.current_block)
        #     self.current_block = BasicBlock()

        return None

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        # ir = Conditional()
        # ir.condition = self.visitParExpression(ctx.parExpression())
        #
        # self.basic_blocks.append(self.current_block)
        # self.current_block = BasicBlock()
        #
        # self.visitBlockStatement(ctx.blockStatement())
        #
        # self.basic_blocks.append(self.current_block)
        # self.current_block = BasicBlock()

        return None

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        # # ir = LoopIR()
        # new_var = ''.join(random.choices(string.ascii_uppercase + string.digits, k=8))
        #
        # # ir.condition = "{} < {}".format(new_var, ctx.INTEGER_LITERAL().__str__())
        #
        # # self.basic_blocks.append(ir)
        # self.current_block = BasicBlock()
        #
        # self.visitBlockStatement(ctx.blockStatement())
        #
        # # decrement.expression = "{} = {}-1".format(new_var, new_var)
        # # self.current_block.add(decrement)
        #
        # self.basic_blocks.append(self.current_block)
        # self.current_block = BasicBlock()

        return None

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "(" + self.visitExpression(ctx.expression()) + ")"

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        # ir = Call()
        # name = ctx.IDENTIFIER().__str__()
        # ir.args = self.symbol_table.functions[name].args
        # ir.uses = ir.args
        # ir.jumps.append(self.symbol_table.functions[name])

        return None

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        # ir = self.visitChildren(ctx)
        # name = ctx.IDENTIFIER().__str__()
        # ir.defs.add(self.symbol_table.get_local(name, self.scope_stack[-1]))
        # self.current_block.add(ir)

        return None

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return self.visitChildren(ctx)

    def visitMix(self, ctx: BSParser.MixContext):

        # ir = Mix()
        # for fluid in ctx.volumeIdentifier():
        #     ir.uses.add(self.visitVolumeIdentifier(fluid)['variable'])

        return None

    def visitDetect(self, ctx: BSParser.DetectContext):
        module = self.register_map[ctx.IDENTIFIER(0).__str__()]
        reagent = self.register_map[ctx.IDENTIFIER(1).__str__()]
        output = {"module": module, "reagent": reagent}
        if ctx.timeIdentifier():
            output['time'] = super().visitTimeIdentifier(ctx.timeIdentifier())

        return output

    def visitHeat(self, ctx: BSParser.HeatContext):
        # ir = Heat()
        # ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        # self.current_block.add(ir)
        return None

    def visitSplit(self, ctx: BSParser.SplitContext):
        # ir = Split()
        # ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        return None

    def visitDispense(self, ctx: BSParser.DispenseContext):
        manifest = ctx.IDENTIFIER().__str__()
        # ir.uses.add(self.symbol_table.get_global(ctx.IDENTIFIER().__str__()))
        # ir = Dispense(self.register_map[])
        return None

    def visitDispose(self, ctx: BSParser.DisposeContext):
        # ir = Dispose()
        # ir.uses.add(self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        # self.current_block.add(ir)
        return None
