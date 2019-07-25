import importlib

import networkx as nx

from compiler.data_structures.basic_block import BasicBlock
from compiler.data_structures.ir import *
from compiler.data_structures.registers import *
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser


class IRVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        # This is the list of *all* basic blocks.
        # This is the blocks which belong to specific functions.
        # This minimally is populated with a 'main'
        self.functions = dict()
        self.current_block = None
        # What is allocated to what.
        self.allocation_map = dict()
        # Global vars.
        self.globalz = dict()
        # Used for controlling the control basic blocks.
        self.control_stack = list()
        # Call stack for the program.
        self.call_stack = list()
        # This is the graph for the *entire* program.
        self.graph = nx.DiGraph()
        # Does this rename vars?
        self.rename = False
        # The function name -> function name mapping.
        self.calls = dict()
        # The BB.nid -> function name mapping.
        self.bb_calls = {'main': list()}
        # Maps the label name to the BB.nid.
        self.labels = dict()

    def add_call(self, source: str, dest: str):
        if source not in self.calls:
            self.calls[source] = set()
        self.calls[source].add(dest)

    def get_register(self, var: Variable, register: str = "Temp"):
        if var.name not in self.allocation_map:
            module = importlib.import_module("compiler.data_structures.registers")
            class_ = getattr(module, register.capitalize())
            instance = class_(var)
            self.allocation_map[var.name] = instance

        return self.allocation_map[var.name]

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")
        self.symbol_table.current_scope = self.symbol_table.scope_map['main']
        # Create the place to store main's basic blocks.
        # self.basic_blocks["main"] = dict()

        self.visitModuleDeclaration(ctx.moduleDeclaration())
        self.visitManifestDeclaration(ctx.manifestDeclaration())
        self.visitStationaryDeclaration(ctx.stationaryDeclaration())

        if ctx.functionDeclaration():
            for func in ctx.functionDeclaration():
                # Add the chain of basic blocks resulting from the functions.
                self.visitFunctionDeclaration(func)
                pass

        # self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block
        self.current_block = BasicBlock()
        self.graph.add_node(self.current_block.nid, function=self.scope_stack[-1])

        self.functions['main'] = {'blocks': dict(), 'entry': self.current_block.nid, 'graph': self.graph}

        # Add all the subsequent instructions to the B.B.
        for i in ctx.statements():
            self.visitStatements(i)

        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        for module in ctx.IDENTIFIER():
            name = module.__str__()
            # self.globalz[name] = Module(self.symbol_table.get_global(name))
            self.globalz[name] = self.symbol_table.get_global(name)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        for manifest in ctx.IDENTIFIER():
            name = manifest.__str__()
            # self.globalz[name] = Global(self.symbol_table.get_global(name))
            self.globalz[name] = self.symbol_table.get_global(name)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        for stationary in ctx.IDENTIFIER():
            name = stationary.__str__()
            # self.globalz[name] = Stationary(self.symbol_table.get_global(name))
            self.globalz[name] = self.symbol_table.get_global(name)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]
        self.functions[name] = dict()
        # initialize the basicblock calling chain.
        self.bb_calls[name] = list()

        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]

        self.current_block = BasicBlock()
        self.functions[name] = {"blocks": dict(), "entry": self.current_block.nid, 'graph': None}
        label = Label("{}_entry".format(name))
        self.labels[label.name] = self.current_block.nid
        self.current_block.add(label)
        self.graph.add_node(self.current_block.nid, function=self.scope_stack[-1])

        for statement in ctx.statements():
            self.visitStatements(statement)

        ret_statement = self.visitReturnStatement(ctx.returnStatement())
        self.current_block.add(ret_statement)
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block
        self.functions[name]['graph'] = self.graph

        self.scope_stack.pop()
        return None

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        if ctx.IDENTIFIER():
            value = self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
        elif ctx.literal():
            value = Number('Constant_{}'.format(self.visitLiteral(ctx.literal())),
                           value=float(self.visitLiteral(ctx.literal())), is_constant=False)
            self.symbol_table.add_local(value, self.scope_stack[-1])
        elif ctx.methodCall():
            value = self.visitMethodCall(ctx.methodCall())
        else:
            value = self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])

        return Return(value, None)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        # Build the conditional for this statement.
        par_expression = self.visitParExpression(ctx.parExpression())
        if BSBaseVisitor.is_number(par_expression['exp1']):
            exp1 = Number("Constant_{}".format(par_expression['exp1']), {ChemTypes.NAT, ChemTypes.REAL},
                          self.scope_stack[-1], value=float(par_expression['exp1']), is_constant=True)
            self.symbol_table.add_local(exp1, self.scope_stack[-1])
        else:
            exp1 = par_expression['exp1']
        if BSBaseVisitor.is_number(par_expression['exp2']):
            exp2 = Number("Constant_{}".format(par_expression['exp2']), {ChemTypes.NAT, ChemTypes.REAL},
                          self.scope_stack[-1], value=float(par_expression['exp2']), is_constant=True)
            self.symbol_table.add_local(exp2, self.scope_stack[-1])
        else:
            exp2 = par_expression['exp2']

        # Build the IR Conditional
        condition = Conditional(par_expression['op'], exp1, exp2)
        self.current_block.add(condition)
        # Build the true block of this statement.
        true_block = BasicBlock()
        true_label = Label("bsbbif_{}_t".format(true_block.nid))
        self.labels[true_label.name] = true_block.nid
        true_block.add(true_label)
        self.graph.add_node(true_block.nid, function=self.scope_stack[-1])
        self.graph.add_edge(self.current_block.nid, true_block.nid)
        condition.true_branch = true_label

        # self.basic_blocks[self.scope_stack[-1]][true_block.nid] = true_block
        self.functions[self.scope_stack[-1]]['blocks'][true_block.nid] = true_block

        # Build the false block of this statement.
        false_block = BasicBlock()
        false_label = Label("bsbbif_{}_f".format(false_block.nid))
        self.labels[false_label.name] = false_block.nid
        false_block.add(false_label)
        self.graph.add_node(false_block.nid, function=self.scope_stack[-1])
        self.graph.add_edge(self.current_block.nid, false_block.nid)
        condition.false_branch = false_label

        # self.basic_blocks[self.scope_stack[-1]][false_block.nid] = false_block
        self.functions[self.scope_stack[-1]]['blocks'][false_block.nid] = false_block

        if not ctx.ELSE():
            join_block = false_block
        else:
            join_block = BasicBlock()
            join_label = Label("bsbbif_{}_j".format(join_block.nid))
            self.labels[join_label.name] = join_block.nid
            join_block.add(join_label)
            self.graph.add_node(join_block.nid, function=self.scope_stack[-1])
            # self.basic_blocks[self.scope_stack[-1]][join_block.nid] = join_block
            self.functions[self.scope_stack[-1]]['blocks'][join_block.nid] = join_block

        # self.current_block.add("Condition")

        # self.basic_blocks[self.scope_stack[-1]][self.current_block.nid] = self.current_block
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        self.current_block = true_block

        # Save the parent join
        self.control_stack.append(join_block)
        # Visit the conditional's statements.
        self.visitBlockStatement(ctx.blockStatement(0))

        join_block = self.control_stack.pop()

        # This check guarantees that a true block will not jump to a join
        # while dealing with nested conditionals.
        if self.control_stack and len(self.graph.edges(true_block.nid)) == 0:
            #true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)
        elif len(self.control_stack) == 0 and len(self.graph.edges(true_block.nid)) == 0:
            #true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)

        if ctx.ELSE():
            # self.basic_blocks[self.scope_stack[-1]][self.current_block.nid] = self.current_block
            self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

            self.control_stack.append(join_block)
            self.current_block = false_block

            self.visitBlockStatement(ctx.blockStatement(1))

            join_block = self.control_stack.pop()
            # This check guarantees that a false block will not jump to a join
            # while dealing with nested conditionals.
            if self.control_stack and len(self.graph.edges(false_block.nid)) == 0:
                #false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)
            elif len(self.control_stack) == 0 and len(self.graph.edges(false_block.nid)) == 0:
                #false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)

        # Add the current join to the parent join.
        if self.control_stack:
            #join_block.add(Jump(self.control_stack[-1].label))
            self.graph.add_edge(join_block.nid, self.control_stack[-1].nid)
            pass

        # self.basic_blocks[self.scope_stack[-1]][self.current_block.nid] = self.current_block
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        self.current_block = join_block

        return NOP()

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        par_expression = self.visitParExpression(ctx.parExpression())

        if BSBaseVisitor.is_number(par_expression['exp1']):
            exp1 = Number("Constant_{}".format(par_expression['exp1']), {ChemTypes.NAT, ChemTypes.REAL},
                          self.scope_stack[-1], value=float(par_expression['exp1']), is_constant=True)
            self.symbol_table.add_local(exp1, self.scope_stack[-1])
        else:
            exp1 = par_expression['exp1']
        if BSBaseVisitor.is_number(par_expression['exp2']):
            exp2 = Number("Constant_{}".format(par_expression['exp2']), {ChemTypes.NAT, ChemTypes.REAL},
                          self.scope_stack[-1], value=float(par_expression['exp2']), is_constant=True)
            self.symbol_table.add_local(exp2, self.scope_stack[-1])
        elif self.symbol_table.get_local(par_expression['exp2']):
            exp2 = self.symbol_table.get_local(par_expression['exp2'])
        else:
            exp2 = par_expression['exp2']

        # finished with this block
        # pre_loop_label = Label("bsbbw_{}_p".format(self.current_block.nid))
        # self.labels[pre_loop_label.name] = self.current_block.nid
        # self.current_block.add(pre_loop_label)
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        # insert header block for the conditional
        header_block = BasicBlock()
        header_label = Label("bsbbw_{}_h".format(header_block.nid))
        self.labels[header_label.name] = header_block.nid
        header_block.add(header_label)
        self.graph.add_node(header_block.nid, function=self.scope_stack[-1])
        self.functions[self.scope_stack[-1]]['blocks'][header_block.nid] = header_block

        # we have a directed edge from current block to the header
        self.graph.add_edge(self.current_block.nid, header_block.nid)

        # the condition goes in the header
        condition = Conditional(par_expression['op'], exp1, exp2)
        header_block.add(condition)

        self.control_stack.append(header_block)

        # set up true block
        true_block = BasicBlock()
        true_label = Label("bsbbw_{}_t".format(true_block.nid))
        self.labels[true_label.name] = true_block.nid
        true_block.add(true_label)
        self.graph.add_node(true_block.nid, function=self.scope_stack[-1])
        self.functions[self.scope_stack[-1]]['blocks'][true_block.nid] = true_block
        condition.true_branch = true_label

        # we have a directed edge from header to true block
        self.graph.add_edge(header_block.nid, true_block.nid)

        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())

        # the block statement may contain nested conditionals
        # If so, the current block is the last false block created for the inner-most conditional
        #    otherwise, the current block is the true_block created above
        # Either way, we can pop the control stack to find where to place the back edge
        #   and immediately make the back edge (from 'current block') to the parent
        parent_block = self.control_stack.pop()
        self.graph.add_edge(self.current_block.nid, parent_block.nid)

        # we now deal with the false branch
        false_block = BasicBlock()

        false_label = Label("bsbbw_{}_f".format(false_block.nid))
        self.labels[false_label.name] = false_block.nid
        false_block.add(false_label)
        condition.false_branch = false_label
        self.graph.add_edge(header_block.nid, false_block.nid)
        # We are done, so we need to handle the book keeping for
        # next basic block generation.
        self.graph.add_node(false_block.nid, function=self.scope_stack[-1])
        self.functions[self.scope_stack[-1]]['blocks'][false_block.nid] = false_block

        self.current_block = false_block

        return NOP()

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        # get the (statically defined!) repeat value
        if ctx.IDENTIFIER() is not None:
            exp = self.symbol_table.get_local(ctx.IDENTIFIER().__str__())
        else:
            exp = Number("REPEAT_{}".format(ctx.INTEGER_LITERAL().__str__()), {ChemTypes.NAT, ChemTypes.REAL},
                          self.scope_stack[-1], value=float(ctx.INTEGER_LITERAL().__str__()), is_constant=True)
        self.symbol_table.add_local(exp, self.scope_stack[-1])

        # finished with this block
        # pre_loop_label = Label("bsbbw_{}_p".format(self.current_block.nid))
        # self.labels[pre_loop_label.name] = self.current_block.nid
        # self.current_block.add(pre_loop_label)
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        # insert header block for the conditional
        header_block = BasicBlock()
        header_label = Label("bsbbr_{}_h".format(header_block.nid))
        self.labels[header_label.name] = header_block.nid
        header_block.add(header_label)
        self.graph.add_node(header_block.nid, function=self.scope_stack[-1])
        self.functions[self.scope_stack[-1]]['blocks'][header_block.nid] = header_block

        # we have a directed edge from current block to the header
        self.graph.add_edge(self.current_block.nid, header_block.nid)

        # the condition goes in the header
        condition = Conditional(RelationalOps.GT, exp, Number(Constant(0), is_constant=True))
        header_block.add(condition)

        self.control_stack.append(header_block)

        # set up the true block
        true_block = BasicBlock()
        true_label = Label("bsbbr_{}_t".format(true_block.nid))
        self.labels[true_label.name] = true_block.nid
        true_block.add(true_label)
        self.graph.add_node(true_block.nid, function=self.scope_stack[-1])
        self.functions[self.scope_stack[-1]]['blocks'][true_block.nid] = true_block
        condition.true_branch = true_label

        # we have a directed edge from header to true block
        self.graph.add_edge(header_block.nid, true_block.nid)

        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())

        # repeat is translated to a while loop as: while (exp > 0);
        # hence, we update exp by decrementing.
        self.current_block.add(BinaryOp(exp, Number(Constant(1), is_constant=True), BinaryOps.SUBTRACT, exp))

        # the block statement may contain nested loops
        # If so, the current block is the last false block created for the inner-most loop
        #    otherwise, the current block is the true_block created above
        # Either way, we can pop the control stack to find where to place the back edge
        #   and immediately make the back edge (from 'current block' to the parent
        parent_block = self.control_stack.pop()
        self.graph.add_edge(self.current_block.nid, parent_block.nid)

        # we now deal with the false branch
        false_block = BasicBlock()

        false_label = Label("bsbbr_{}_f".format(false_block.nid))
        self.labels[false_label.name] = false_block.nid
        false_block.add(false_label)
        condition.false_branch = false_label
        self.graph.add_edge(header_block.nid, false_block.nid)
        # We are done, so we need to handle the book keeping for
        # next basic block generation.
        self.graph.add_node(false_block.nid, function=self.scope_stack[-1])
        self.functions[self.scope_stack[-1]]['blocks'][false_block.nid] = false_block

        self.current_block = false_block

        return NOP()

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return self.visitExpression(ctx.expression())

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        args = list()
        for expr in ctx.expression():
            arg = self.visitExpression(expr)
            if self.is_number(arg):
                number = Number("Constant_{}".format(arg), {ChemTypes.NAT, ChemTypes.REAL},
                                self.scope_stack[-1], value=float(arg), is_constant=True)
                self.symbol_table.add_local(number, self.scope_stack[-1])
                args.append(number)
            else:
                args.append(self.symbol_table.get_local(arg, self.scope_stack[-1]))

        return args

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        name = ctx.IDENTIFIER().__str__()
        return {"args": self.visitExpressionList(ctx.expressionList()), "func": self.symbol_table.functions[name],
                "op": IRInstruction.CALL}

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        details = self.visitChildren(ctx)
        var = self.symbol_table.get_local(ctx.IDENTIFIER().__str__(), self.scope_stack[-1])
        # self.allocation_map[var.name] = var
        # self.current_block.add_defs(var)

        if 'op' not in details:
            if self.is_number(details):
                ir = Store(var, float(details))
            else:
                ir = Store(var, self.symbol_table.get_local(details, self.scope_stack[-1]))
                # self.current_block.add_uses(self.symbol_table.get_local(details))
        elif details['op'] == IRInstruction.MIX:
            ir = Mix(var, details['reagents'][0], details['reagents'][1])
        elif details['op'] == IRInstruction.SPLIT:
            ir = Split(var, details['reagents'][0], details['size'])
        elif details['op'] == IRInstruction.DISPENSE:
            ir = Dispense(var, details['reagents'][0])
        elif details['op'] == IRInstruction.CALL:
            ir = Call(var, details['func'], details['args'])
        elif details['op'] == IRInstruction.DETECT:
            ir = Detect(var, details['module'], details['reagents'][0])
        elif details['op'] in InstructionSet.BinaryOps:
            ir = BinaryOp(details['exp1'], details['exp2'], details['op'], var)
        else:
            ir = NOP()

        self.current_block.add(ir)
        if ir.op == IRInstruction.CALL:
            # Make the call.
            self.bb_calls[self.scope_stack[-1]].append((self.current_block.nid, ir.function.name))
            # Save the block.
            self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block
            # We need to initialize a new block.
            next_block = BasicBlock()
            next_block.add(Label("{}_return".format(ir.function.name)))
            self.graph.add_node(next_block.nid, function=self.scope_stack[-1])
            self.graph.add_edge(self.current_block.nid, next_block.nid)
            # Point to the new block.
            self.current_block = next_block
            # Add the call.
            self.add_call(self.scope_stack[-1], ir.function.name)

        return ir

    # def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
    #     return self.visitChildren(ctx)

    def visitMix(self, ctx: BSParser.MixContext):

        if ctx.timeIdentifier():
            temp_time = self.visitTimeIdentifier(ctx.timeIdentifier())
            time = (temp_time['quantity'], temp_time['units'])
        else:
            time = (10, BSTime.SECOND)

        reagent1 = self.visitVolumeIdentifier(ctx.volumeIdentifier(0))['variable']
        reagent2 = self.visitVolumeIdentifier(ctx.volumeIdentifier(1))['variable']

        reagents = [reagent1, reagent2]

        return {"reagents": reagents, "execute_for": time, "op": IRInstruction.MIX}

    def visitDetect(self, ctx: BSParser.DetectContext):
        module = self.globalz[ctx.IDENTIFIER(0).__str__()]
        variable = self.symbol_table.get_local(self.rename_var(ctx.IDENTIFIER(1).__str__()), self.scope_stack[-1])
        # self.current_block.add_uses(variable)

        if ctx.timeIdentifier():
            time = super().visitTimeIdentifier(ctx.timeIdentifier())
        else:
            time = (10, BSTime.SECOND)

        return {"module": module, "reagents": [variable], "execute_for": time, "op": IRInstruction.DETECT}

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_local(self.rename_var(ctx.IDENTIFIER().__str__()), self.scope_stack[-1])
        # self.current_block.add_uses(variable)
        # self.current_block.add_defs(variable)
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
        else:
            time = (10, BSTime.SECOND)
        ir = Heat(variable, variable)
        self.current_block.add(ir)
        return ir

    def visitSplit(self, ctx: BSParser.SplitContext):
        variable = self.symbol_table.get_local(self.rename_var(ctx.IDENTIFIER().__str__()), self.scope_stack[-1])
        # self.current_block.add_uses(variable)
        size = int(ctx.INTEGER_LITERAL().__str__())
        return {"reagents": [variable], "size": size, "op": IRInstruction.SPLIT}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        variable = self.symbol_table.get_local(self.rename_var(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]))
        return {"reagents": [variable], "op": IRInstruction.DISPENSE}

    def visitDispose(self, ctx: BSParser.DisposeContext):
        variable = self.symbol_table.get_local(self.rename_var(ctx.IDENTIFIER().__str__()), self.scope_stack[-1])
        # self.current_block.add_uses(variable)
        # TODO: Attempt to calculate the number of disposal registers (i.e. number of ports.)
        ir = Dispose(variable, variable)
        self.current_block.add(ir)
        return ir
