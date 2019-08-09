import networkx as nx

from compiler.data_structures.basic_block import BasicBlock
from compiler.data_structures.ir import *
from compiler.data_structures.variable import Stationary, Number, Module, Dispensable, Movable
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import InvalidOperation


class IRVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "Basic Block Visitor")
        # This is the list of *all* basic blocks.
        # This is the blocks which belong to specific functions.
        # This minimally is populated with a 'main'
        self.functions = dict()
        self.current_block = None
        # Global vars.
        self.globalz = dict()
        # Used for controlling the control basic blocks.
        self.control_stack = list()
        # Call stack for the program.
        # self.call_stack = list()
        # This is the graph for the *entire* program.
        self.graph = nx.DiGraph()
        # The function name -> function name mapping.
        self.calls = dict()
        # The BB.nid -> function name mapping.
        self.bb_calls = {'main': list()}
        # Maps the label name to the BB.nid.
        self.labels = dict()
        self.registers = dict()

    def add_call(self, source: str, dest: str):
        if source not in self.calls:
            self.calls[source] = set()
        self.calls[source].add(dest)

    def check_bounds(self, var: Dict) -> bool:
        # Make one last-ditch effort to find the symbol.
        if var['var'] is None:
            var['var'] = self.symbol_table.get_symbol(var['name'])
        # If there isn't a value, assume all is good.
        if not var['var']:
            return True
        if var['index'] >= var['var'].size:
            raise InvalidOperation("{}[{}] is out of bounds, which has a size of {}"
                                   .format(var['var'].name, var['index'], var['var'].size))
        return True

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")
        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

        for header in ctx.globalDeclarations():
            self.visitGlobalDeclarations(header)

        if ctx.functions():
            self.visitFunctions(ctx.functions())

        # Set the current block to a new block *after* the functions.
        self.current_block = BasicBlock()
        self.current_block.label = "main"
        self.graph.add_node(self.current_block.nid, function=self.scope_stack[-1])
        # Build the main function.
        self.functions['main'] = {'blocks': dict(), 'entry': self.current_block.nid, 'graph': self.graph}

        # Add all the subsequent instructions to the B.B.
        for statement in ctx.statements():
            self.visitStatements(statement)

        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        symbol = self.symbol_table.get_global(name)
        self.globalz[name] = Module(name)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        symbol = self.symbol_table.get_global(name)
        self.globalz[name] = Dispensable(name)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        symbol = self.symbol_table.get_global(name)
        self.globalz[name] = Stationary(name)

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
            # true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)
        elif len(self.control_stack) == 0 and len(self.graph.edges(true_block.nid)) == 0:
            # true_block.add(Jump(join_block.label))
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
                # false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)
            elif len(self.control_stack) == 0 and len(self.graph.edges(false_block.nid)) == 0:
                # false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)

        # Add the current join to the parent join.
        if self.control_stack:
            # join_block.add(Jump(self.control_stack[-1].label))
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

    def visitStore(self, ctx: BSParser.StoreContext):
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})
        if use['index'] == -1:
            use['index'] = use_var.value.size
        if use['index'] == 0:
            use['index'] = 1
        use_indices = list(use_var.value.value.keys())
        for x in range(use['index']):
            ir = Store({"name": use['name'], 'offset': use_indices[x]})
            self.current_block.add(ir)

    def visitNumberAssignment(self, ctx: BSParser.NumberAssignmentContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        value = self.visitLiteral(ctx.literal())
        size = 1 if deff['index'] == -1 else deff['index']
        variable = Number(deff['name'], size, value)
        for x in range(size):
            ir = Constant({'name': deff['name'], 'offset': x}, value)
            self.current_block.add(ir)
        # The numerical equivalent of a dispense.
        self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).value = variable
        return None

    def visitMath(self, ctx: BSParser.MathContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        deff_var = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])
        if deff_var.value is not None:
            self.check_bounds({'name': deff['name'], 'index': deff['index'], 'var': deff_var})
        deff_offset = 0 if deff['index'] == -1 else deff['index']

        op1 = self.visitPrimary(ctx.primary(0))
        if 'value' in op1.keys():
            op1_var = self.symbol_table.get_global('CONST_{}'.format(op1['value'])).value
        else:
            op1_var = self.symbol_table.get_local(op1['name'], self.scope_stack[-1]).value
        self.check_bounds({'name': op1['name'], 'index': op1['index'], 'var': op1_var})

        op2 = self.visitPrimary(ctx.primary(1))
        if 'value' in op2.keys():
            op2_var = self.symbol_table.get_global('CONST_{}'.format(op2['value'])).value
        else:
            op2_var = self.symbol_table.get_local(op2['name'], self.scope_stack[-1]).value
        self.check_bounds({'name': op2['name'], 'index': op2['index'], 'var': op2_var})

        op1_offset = 0 if op1['index'] == -1 else op1['index']
        op2_offset = 0 if op2['index'] == -1 else op2['index']

        outcome = 0
        if ctx.ADDITION():
            operand = BinaryOps.ADD
            outcome = op1_var.value[op1_offset] + op2_var.value[op2_offset]
        elif ctx.SUBTRACT():
            operand = BinaryOps.SUBTRACT
            outcome = op1_var.value[op1_offset] - op2_var.value[op2_offset]
        elif ctx.DIVIDE():
            operand = BinaryOps.DIVIDE
            outcome = op1_var.value[op1_offset] / op2_var.value[op2_offset]
        elif ctx.MULTIPLY():
            operand = BinaryOps.MULTIPLE
            outcome = op1_var.value[op1_offset] * op2_var.value[op2_offset]
        else:
            operand = BinaryOps.ADD
            outcome = op1_var.value[op1_offset] + op2_var.value[op2_offset]

        ir = Math({'name': deff['name'], 'offset': deff_offset},
                  {'name': op1_var.name, 'offset': op1_offset},
                  {'name': op2_var.name, 'offset': op2_offset},
                  operand)
        self.current_block.add(ir)

        if deff_var.value is None:
            deff_var.value = Number(deff['name'], value=outcome)

        return None

    def visitMix(self, ctx: BSParser.MixContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        symbol = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])

        if ctx.timeIdentifier():
            temp_time = self.visitTimeIdentifier(ctx.timeIdentifier())
            time = (temp_time['quantity'], temp_time['units'])
        else:
            time = (10, BSTime.SECOND)

        uses = list()
        for fluid in ctx.variable():
            use = self.visitVariable(fluid)
            var = self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value
            uses.append({'var': var, 'index': use['index'], 'name': use['name']})
        use_a = uses[0]
        use_b = uses[1]

        # Get the time modifier, should one exist.
        time_meta = None
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            time_meta = TimeConstraint(IRInstruction.MIX, time['quantity'], time['units'])

        '''
        Cases that need to be considered:
        1) a = dispense aaa
            b = dispense bbb
            c = mix(a, b)
            (all indices are -1 *and* size = 1)

        2) a[n] = dispense aaa
            b[m] = dispense bbb
            c = mix(a[x], b[y]) 
            (index(c) == -1, index(a) == x, index(b) == y, *and* size = 1)

        3) a[n] = dispense aaa
            b[n] = dispense bbb
            c = mix(a, b) 
            (index(c) == -1, index(a) == -1, index(b) == -1, *and* size(a || b) == length(a || b))
        '''
        size = 1
        # Check for the case where we are mixing two arrays into one.
        if (use_a['index'] == -1 and use_a['var'].size > 1) and (use_b['index'] == -1 and use_b['var'].size > 1):
            if use_a['var'].size != use_b['var'].size:
                raise InvalidOperation("{} is not the same size as {}".format(use_a['var'].name, use_b['var'].name))
            # This abstraction allows us to use all the indices that
            # are currently available in the array, so if there
            # was a case where gaps existed between index 1 and 3,
            # but the sizes still matched, this covers that case.
            use_a_index = list(use_a['var'].value.keys())
            use_b_index = list(use_b['var'].value.keys())
            size = use_a['var'].size

            # Add the instructions to the basic block.
            for x in range(use_a['var'].size):
                ir = Mix({'name': deff['name'], 'offset': x},
                         {'name': use_a['var'].name, 'offset': use_a_index[x]},
                         {'name': use_b['var'].name, 'offset': use_b_index[x]})
                # Add the time constraint if there is one.
                if time_meta:
                    ir.meta.append(time_meta)
                self.current_block.add(ir)
        else:
            # Check the bounds of the inputs.
            self.check_bounds(use_a)
            self.check_bounds(use_b)
            # Get the offsets of the uses.
            use_a_offset = 0 if use_a['index'] == -1 else use_a['index']
            use_b_offset = 0 if use_b['index'] == -1 else use_b['index']
            deff_offset = 0 if deff['index'] == -1 else deff['index']

            # If there is value, then we know this is a SISD instruction,
            # and it takes the form a[x] = mix...
            if symbol.value is not None:
                ir = Mix({'name': deff['name'], 'offset': deff_offset},
                         {'name': use_a['var'].name, 'offset': use_a_offset},
                         {'name': use_b['var'].name, 'offset': use_b_offset})
            else:
                ir = Mix({'name': deff['name'], 'offset': 0},
                         {'name': use_a['var'].name, 'offset': use_a_offset},
                         {'name': use_b['var'].name, 'offset': use_b_offset})
            # Add the time constraint should one exist.
            if time_meta:
                ir.meta.append(time_meta)
            self.current_block.add(ir)

        if not symbol.value:
            # Update the symbol in the symbol table with the new value.
            symbol.value = Movable(deff['name'], size)

        return None

    def visitDetect(self, ctx: BSParser.DetectContext):
        """
        Cases to consider:
        1) a = dispense aaa
            x = detect mod on a
        2) a[n] = dispense aaa
            x = detect mod on a[m]
        3) a[n] = dispense aaa
            x = detect mod on a
        :param ctx:
        :return:
        """
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        symbol = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])

        time_meta = None
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            time_meta = TimeConstraint(IRInstruction.DETECT, time['quantity'], time['units'])

        module = self.symbol_table.get_global(ctx.IDENTIFIER().__str__())
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        self.check_bounds({'index': use['index'], 'name': use_var.name, 'var': use_var.value})
        if use['index'] == -1:
            use['index'] = use_var.value.size
        if use['index'] == 0:
            use['index'] = 1
        use_indices = list(use_var.value.value.keys())
        for x in range(use['index']):
            ir = Detect({"name": deff['name'], 'offset': x},
                        {'name': module.name, 'offset': 0},
                        {'name': use['name'], 'offset': use_indices[x]})
            if time_meta is not None:
                ir.meta.append(time_meta)
            self.current_block.add(ir)

        if symbol.value is None:
            symbol.value = Number(deff['name'], use_var.value.size)

        return None

    def visitHeat(self, ctx: BSParser.HeatContext):
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        # if use['index'] == -1:
        #     use['index'] = self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value.size

        time = None
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())

        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())

        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})
        if use['index'] == -1:
            use['index'] = use_var.value.size
        if use['index'] == 0:
            use['index'] = 1

        for x in range(use['index']):
            val = {'name': use['name'], 'offset': x}
            ir = Heat(val, val)
            if time is not None:
                ir.meta.append(TimeConstraint(IRInstruction.HEAT, time[0], time[1]))
            ir.meta.append(TempConstraint(IRInstruction.HEAT, temp['quantity'], temp['units']))
            self.current_block.add(ir)
        # We don't need to add a value to whatever symbol is being used.
        # There is nothing being created, thus, no symbol to attach a value.
        return None

    def visitSplit(self, ctx: BSParser.SplitContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        symbol = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])

        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])
        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})

        split_num = int(ctx.INTEGER_LITERAL().__str__())

        ir = Split({'name': deff['name'], 'offset': -1}, {'name': use['name'], 'offset': use['index']}, split_num)
        self.current_block.add(ir)

        if symbol.value is None:
            symbol.value = Movable(deff['name'], size=split_num * use_var.value.size)

        return None

    def visitDispense(self, ctx: BSParser.DispenseContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())

        if deff['index'] == -1 or deff['index'] == 0:
            deff['index'] = 1

        for x in range(deff['index']):
            self.current_block.add(Dispense({'name': deff['name'], 'offset': x},
                                            {'name': ctx.IDENTIFIER().__str__(), 'offset': 1}))

        # We don't have to check here, because this is a dispense.
        self.symbol_table.get_local(deff['name']).value = Movable(deff['name'], size=deff['index'], volume=10.0)

        return None

    def visitDispose(self, ctx: BSParser.DisposeContext):
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})
        if use['index'] == -1:
            use['index'] = use_var.value.size
        if use['index'] == 0:
            use['index'] = 1
        use_indices = list(use_var.value.value.keys())
        for x in range(use['index']):
            ir = Dispose({"name": use['name'], 'offset': use_indices[x]})
            self.current_block.add(ir)

        return None
