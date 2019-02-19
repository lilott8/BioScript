import networkx as nx

from compiler.data_structures.basic_block import BasicBlock
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from compiler.symbol_table.symbol_table import SymbolTable
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *


class SymbolVisitorV2(BSBaseVisitor):

    def __init__(self, symbol_table: SymbolTable):
        super().__init__(symbol_table, "SymbolTable 2: Electric Boogaloo")
        self.graph = nx.DiGraph()
        self.basic_blocks = dict()
        self.current_block = None
        self.previous_block = None
        self.control_stack = list()
        self.in_control = {"if": False, "while": False, "repeat": False}

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")

        if ctx.functionDeclaration():
            for func in ctx.functionDeclaration():
                # Add the chain of basic blocks resulting from the functions.
                # self.visitFunctionDeclaration(func)
                pass
            # self.basic_blocks[self.current_block.nid] = self.current_block

        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

        self.current_block = BasicBlock()
        self.graph.add_node(self.current_block.nid)

        # Add all the subsequent instructions to the B.B.
        for i in ctx.statements():
            self.visitStatements(i)

        self.basic_blocks[self.current_block.nid] = self.current_block

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()

        self.scope_stack.append(name)
        # This sets the current scope.  At this point,
        # The scope should have been created by now.
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]

        self.previous_block = self.current_block
        self.current_block = BasicBlock()
        self.graph.add_node(self.current_block.nid)

        for s in ctx.statements():
            self.visitStatements(s)

        return_data = self.visitReturnStatement(ctx.returnStatement())
        self.current_block.add(return_data)

        self.scope_stack.pop()

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        return "RETURN"

    def visitBlockStatement(self, ctx: BSParser.BlockStatementContext):
        return super().visitBlockStatement(ctx)

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return super().visitVariableDeclaration(ctx)

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return super().visitStatements(ctx)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        """
        :param ctx:
        :return:
        """
        """
        1) Add current instruction to current block
        2) Create true block
        3) AddEdge(current, true)
        4) Push true block onto stack
        5) Visit true statements
        6) Pop true block
        7) repeat 2-6 for false
        """
        if self.in_control["if"]:
            raise UnsupportedOperation("We do not currently support nested conditionals.")

        self.in_control["if"] = True
        true_block = BasicBlock()
        self.graph.add_node(true_block.nid)
        self.graph.add_edge(self.current_block.nid, true_block.nid)
        true_block.add("bsbbi_{}_t".format(self.current_block.nid))

        false_block = BasicBlock()
        self.graph.add_node(false_block.nid)
        self.graph.add_edge(self.current_block.nid, false_block.nid)
        false_block.add("bsbbi_{}_f".format(false_block.nid))

        self.current_block.add("Condition")
        self.basic_blocks[self.current_block.nid] = self.current_block
        self.current_block = true_block
        # Save the parent control node
        self.control_stack.append(self.current_block)
        # Save the previous block
        # self.previous_block = self.current_block
        # Set the current block to the true branch.
        # self.current_block = true_block
        # Visit the conditional's statements.
        self.visitBlockStatement(ctx.blockStatement(0))
        true_block = self.control_stack.pop()

        from_else = False
        if ctx.ELSE():
            self.basic_blocks[self.current_block.nid] = self.current_block
            self.current_block = false_block
            self.control_stack.append(self.current_block)
            self.visitBlockStatement(ctx.blockStatement(1))
            false_block = self.control_stack.pop()
            from_else = True

        if from_else:
            self.basic_blocks[self.current_block.nid] = self.current_block
            # add the join.
            join_block = BasicBlock()
            join_block.add("bsbbi_{}_j".format(join_block.nid))
            self.graph.add_node(join_block.nid)
            self.graph.add_edge(false_block.nid, join_block.nid)
            self.graph.add_edge(true_block.nid, join_block.nid)
            self.current_block = join_block
        else:
            self.current_block.add("bsbbi_{}_f".format(false_block.nid))

        self.in_control["if"] = False
        return ""

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        # Condition is added to self.current_block.
        if self.in_control["while"]:
            raise UnsupportedOperation("We do not currently support nested conditionals.")
        self.in_control["while"] = True

        true_block = BasicBlock()
        self.graph.add_node(true_block.nid)
        true_block.add("bsbbw_{}_t".format(self.current_block.nid))

        false_block = BasicBlock()
        self.graph.add_node(false_block.nid)
        false_block.add("bsbbw_{}_f".format(false_block.nid))

        self.current_block.add("while condition")
        # If condition evaluates true.
        self.graph.add_cycle([true_block.nid, self.current_block.nid])
        # If condition evaluates false.
        self.graph.add_edge(self.current_block.nid, false_block.nid)
        self.basic_blocks[self.current_block] = self.current_block
        self.previous_block = self.current_block
        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())

        self.basic_blocks[self.current_block.nid] = self.current_block
        self.previous_block = self.current_block
        self.current_block = BasicBlock()
        self.graph.add_edge(false_block.nid, self.current_block.nid)

        self.in_control["while"] = False
        return super().visitWhileStatement(ctx)

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        true_block = BasicBlock()
        self.graph.add_node(true_block.nid)
        self.graph.add_edge(self.current_block.nid, true_block.nid)
        self.basic_blocks[self.current_block.nid] = self.current_block

        false_block = BasicBlock()
        self.graph.add_node(false_block.nid)
        self.control_stack.append(false_block)

        self.visitBlockStatement(ctx.blockStatement())

        return ""


    def visitMix(self, ctx: BSParser.MixContext):
        x = self.visitVolumeIdentifier(ctx.volumeIdentifier(0))['variable'].name
        y = self.visitVolumeIdentifier(ctx.volumeIdentifier(1))['variable'].name
        return "mix {}, {}".format(x, y)

    def visitDetect(self, ctx: BSParser.DetectContext):
        return "detect {}({})".format(ctx.IDENTIFIER(0).__str__(), ctx.IDENTIFIER(1).__str__())

    def visitHeat(self, ctx: BSParser.HeatContext):
        self.current_block.add("heat {}".format(ctx.IDENTIFIER().__str__()))

    def visitSplit(self, ctx: BSParser.SplitContext):
        return "split {}".format(ctx.IDENTIFIER().__str__())

    def visitDispense(self, ctx: BSParser.DispenseContext):
        return "dispense {}".format(ctx.IDENTIFIER().__str__())

    def visitDispose(self, ctx: BSParser.DisposeContext):
        self.current_block.add("dispose {}".format(ctx.IDENTIFIER().__str__()))
        return None

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return super().visitParExpression(ctx)

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        return "call " + ctx.IDENTIFIER().__str__()

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        details = self.visitChildren(ctx)
        self.current_block.add(details + " " + self.visitChildren(ctx))
        return None
