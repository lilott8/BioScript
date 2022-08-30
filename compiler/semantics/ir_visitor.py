from copy import deepcopy

import networkx as nx
from networkx.classes.function import add_cycle
from chemicals.chemtypes import ChemTypeResolver
from compiler.data_structures.basic_block import BasicBlock
from compiler.data_structures.ir import *
from compiler.data_structures.variable import Stationary, Number, Module, Dispensable, Movable, Reagent
from compiler.data_structures.properties import BSVolume
from compiler.data_structures.variable import Symbol
from compiler.semantics.bs_base_visitor import BSBaseVisitor
from antlr4 import *
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import InvalidOperation
import os


class IRVisitor(BSBaseVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "IR Visitor")
        # This is the list of *all* basic blocks.
        # This is the blocks which belong to specific functions.
        # This minimally is populated with a 'main'
        self.functions = dict()
        self.current_block = None
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

    def get_entry_block(self, method_name: str) -> Dict:
        nid = self.labels[method_name]
        return {'label': self.functions[method_name]['blocks'][nid].label, 'nid': nid}

    def check_bounds(self, var: Dict) -> bool:
        # Make one last-ditch effort to find the symbol.
        if var['var'] is None:
            var['var'] = self.symbol_table.get_symbol(var['name']).value
        # If there isn't a value, assume all is good.
        if not var['var']:
            return True
        if var['index'] >= var['var'].size:
            raise InvalidOperation("{}[{}] is out of bounds, which has a size of {}"
                                   .format(var['var'].name, var['index'], var['var'].size))
        return True

    def add_call_to_graph(self, nid: int, function: str):
        if nid not in self.calls.keys():
            self.calls[nid] = set()
        self.calls[nid].add(function)

    def visitProgram(self, ctx: BSParser.ProgramContext):
        self.scope_stack.append("main")
        self.symbol_table.current_scope = self.symbol_table.scope_map['main']

        for header in ctx.globalDeclarations():
            self.visitGlobalDeclarations(header)

        if ctx.functions():
            self.visitFunctions(ctx.functions())

        # Set the current block to a new block *after* the functions.
        self.current_block = BasicBlock()
        self.labels['main'] = self.current_block.nid
        self.current_block.label = Label("main")
        self.graph.add_node(self.current_block.nid, function=self.scope_stack[-1], label=self.current_block.label.label)
        # Build the main function.
        self.functions['main'] = {'blocks': dict(), 'entry': self.current_block.nid, 'graph': self.graph}

        # Add all the subsequent instructions to the B.B.
        for statement in ctx.statements():
            self.visitStatements(statement)

        self.current_block.add(NOP())
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        # Add the graph edges for function calls.
        for key, val in self.calls.items():
            for v in val:
                add_cycle(self.graph, [key, self.functions[v]['entry']])
                #self.graph.add_cycle([key, self.functions[v]['entry']])

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        symbol = self.symbol_table.get_global(name)
        symbol.value = Module(name)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        symbol = self.symbol_table.get_global(name)
        symbol.value = Dispensable(name)

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        symbol = self.symbol_table.get_global(name)
        symbol.value = Stationary(name)

    def visitFromLibrary(self, ctx: BSParser.FromLibraryContext):
        lib_names = ctx.IDENTIFIER()
        return lib_names.symbol.text

    def import_bioscript_function(self, filename, prefix=""):
        file_stream = FileStream(filename)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        tree = parser.functionDeclaration()
        self.visitFunctionDeclaration(tree, prefix)

    def import_compiled_function(self, filename, prefix=""):
        name = prefix+filename.split('/')[-1].split('.')[0]
        self.functions[name] = dict()
        self.bb_calls[name] = list()
        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]
        self.current_block = BasicBlock()
        self.functions[name] = {"blocks": dict(), "entry": self.current_block.nid, 'graph': None}
        label = Label("{}_entry".format(name))
        # Build the mapping from label to nid.
        self.labels[name] = self.current_block.nid
        self.current_block.add(label)
        self.graph.add_node(self.current_block.nid, function=self.scope_stack[-1], label=self.current_block.label.label)

        # pre-compiled, so no statements to deal with.

        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block
        self.functions[name]['graph'] = self.graph

        self.scope_stack.pop()
        return None

    def visitImportFuncFromLibrary(self, ctx: BSParser.ImportFuncFromLibraryContext):
        lib_name = self.visitFromLibrary(ctx.fromLibrary())
        # TODO can just check path for lib name, rather than requiring install at $bioscriptpath
        from_lib_path = os.environ[str("BIOSCRIPTPATH")] + '/' + lib_name
        func_names = [i.__str__() for i in ctx.IDENTIFIER()]

        for file_name in os.listdir(from_lib_path):
            if file_name.__contains__('.') and file_name.split('.')[0] in func_names:
                if file_name.endswith('.bsf'):
                    self.import_bioscript_function(from_lib_path+'/'+file_name)
                elif file_name.endswith('.sbsf'):
                    self.import_compiled_function(from_lib_path+'/'+file_name)
                else:
                    raise FileNotFoundError
        pass

    def visitImportLibrary(self, ctx: BSParser.ImportLibraryContext):
        lib_name = ctx.IDENTIFIER().__str__()
        lib_path = os.environ[str("BIOSCRIPTPATH")] + '/' + lib_name
        # identify all names in library so we can call, e.g.: lib.func_name()
        for file_name in os.listdir(lib_path):
            if file_name.endswith('.bsf'):
                self.import_bioscript_function(lib_path + '/' + file_name, lib_name + '.')
            elif file_name.endswith('.sbsf'):
                self.import_compiled_function(lib_path + '/' + file_name, lib_name + '.')
        pass

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext, prefix=''):
        name = prefix+ctx.IDENTIFIER().__str__()
        self.functions[name] = dict()
        # initialize the basic block calling chain.
        self.bb_calls[name] = list()
        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]
        self.current_block = BasicBlock()
        self.functions[name] = {"blocks": dict(), "entry": self.current_block.nid, 'graph': None}
        label = Label("{}_entry".format(name))
        # Build the mapping from label to nid.
        self.labels[name] = self.current_block.nid
        self.current_block.add(label)
        self.graph.add_node(self.current_block.nid, function=self.scope_stack[-1], label=self.current_block.label.label)

        for statement in ctx.statements():
             self.visitStatements(statement)

        if ctx.returnStatement():
            ret_statement = self.visitReturnStatement(ctx.returnStatement())
            self.log.info(ret_statement)
            if ret_statement['function']:
                ret_val = "{}_return".format(ret_statement['name'])
                self.current_block.add(Call({'name': ret_val, 'offset': -1},
                                            self.symbol_table.functions[ret_statement['name']], ret_statement['args']))
                self.current_block.add(Return({'name': ret_val, 'offset': -1}))
                self.add_call_to_graph(self.current_block.nid, ret_statement['name'])
            else:
                self.current_block.add(Return(ret_statement))

        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block
        self.functions[name]['graph'] = self.graph

        self.scope_stack.pop()
        return None

    def visitReturnStatement(self, ctx: BSParser.ReturnStatementContext):
        if ctx.methodCall():
            method_name, args = self.visitMethodCall(ctx.methodCall())
            var = {'name': method_name, 'size': -1, 'function': True, 'offset': 0, 'args': args}
        else:
            var = self.visitPrimary(ctx.primary())
            var['function'] = False
            var['var'] = self.symbol_table.get_symbol(var['name'], self.scope_stack[-1]).value
            self.check_bounds(var)
            if var['index'] == -1 and var['var'].size > 1:
                var['offset'] = -1
                var['size'] = var['var'].size
            else:
                var['offset'] = 0 if var['index'] == -1 else var['index']
                var['size'] = 1
        return var

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        binops = list()
        for binop in ctx.binops():
            bop = self.visitBinops(binop)
            binops.append(BinaryOp(bop['op1'], bop['op2'], bop['operand']))
        return binops

    def visitBinops(self, ctx: BSParser.BinopsContext):
        op1 = self.visitPrimary(ctx.primary(0))
        op2 = self.visitPrimary(ctx.primary(1))

        op1_var = self.symbol_table.get_symbol(op1['name'], self.scope_stack[-1])
        op2_var = self.symbol_table.get_symbol(op2['name'], self.scope_stack[-1])

        if (op1['index'] == -1 and op1_var.value.size > 1) or (op2['index'] == -1 and op2_var.value.size > 1):
            raise InvalidOperation("You provided an array to condition; you must provide a valid offset.")

        # This must come after the conditional above.  Otherwise,
        # there is no guarantee we mantain syntactic fidelity.
        op1['index'] = 0 if op1['index'] == -1 else op1['index']
        op2['index'] = 0 if op2['index'] == -1 else op2['index']

        self.check_bounds({'name': op1['name'], 'index': op1['index'], 'var': op1_var.value})
        self.check_bounds({'name': op2['name'], 'index': op2['index'], 'var': op2_var.value})

        if ctx.EQUALITY():
            operand = RelationalOps.EQUALITY
        elif ctx.NOTEQUAL():
            operand = RelationalOps.NE
        elif ctx.LT():
            operand = RelationalOps.LT
        elif ctx.LTE():
            operand = RelationalOps.LTE
        elif ctx.GT():
            operand = RelationalOps.GT
        elif ctx.GTE():
            operand = RelationalOps.GTE
        else:
            operand = RelationalOps.EQUALITY

        return {"op1": {'var': op1_var, 'offset': op1['index'], 'name': op1_var.name, 'size': op1_var.value.size},
                "op2": {'var': op2_var, 'offset': op2['index'], 'name': op2_var.name, 'size': op1_var.value.size},
                'operand': operand}

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        # This oddly specific check handles the case where a while loop nested in an if block
        # wouldn't have its false edge connect to the if block's false node.  This, in particular,
        # removes the naive edge that is added as there are still conditional statements that follow.
        # if "_f" in self.current_block.label.label and len(self.control_stack) == 1 and \
        #         self.graph.out_edges(self.current_block.nid):
        #     if (self.current_block.nid, self.control_stack[-1].nid) in self.graph.out_edges(self.current_block.nid):
        #         self.graph.remove_edge(self.current_block.nid, self.control_stack[-1].nid)

        # Build the conditional for this statement.
        cond = self.visitParExpression(ctx.parExpression())
        # Build the IR Conditional
        condition = Conditional(cond[0].op, cond[0].left, cond[0].right)
        self.current_block.add(condition)
        # Build the true block of this statement.
        true_block = BasicBlock()
        true_label = Label("bsbbif_{}_t".format(true_block.nid))
        self.labels[true_label.name] = true_block.nid
        true_block.add(true_label)
        self.graph.add_node(true_block.nid, function=self.scope_stack[-1], label=true_label.label)
        self.graph.add_edge(self.current_block.nid, true_block.nid)
        condition.true_branch = true_label

        # self.basic_blocks[self.scope_stack[-1]][true_block.nid] = true_block
        self.functions[self.scope_stack[-1]]['blocks'][true_block.nid] = true_block

        # Build the false block of this statement.
        false_block = BasicBlock()
        false_label = Label("bsbbif_{}_f".format(false_block.nid))
        self.labels[false_label.name] = false_block.nid
        false_block.add(false_label)
        self.graph.add_node(false_block.nid, function=self.scope_stack[-1], label=false_label.label)
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
            self.graph.add_node(join_block.nid, label=join_label.label, function=self.scope_stack[-1])
            self.functions[self.scope_stack[-1]]['blocks'][join_block.nid] = join_block

        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        self.current_block = true_block

        # Save the parent join
        self.control_stack.append(join_block)
        # Visit the conditional's statements.
        self.visitBlockStatement(ctx.blockStatement(0))

        join_block = self.control_stack.pop()

        '''
        Marked for deletion.
        # This check guarantees that a true block will not jump to a join
        # while dealing with nested conditionals.  If the number of out
        # edges is greater than 0, then we
        # if len(self.graph.edges(true_block.nid)) == 0:
        #     true_block.add(Jump(join_block.label))
        #     self.graph.add_edge(true_block.nid, join_block.nid)
        '''

        if self.control_stack and len(self.graph.edges(true_block.nid)) == 0:
            # true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)
        elif len(self.control_stack) == 0 and len(self.graph.edges(true_block.nid)) == 0:
            # true_block.add(Jump(join_block.label))
            self.graph.add_edge(true_block.nid, join_block.nid)

        if ctx.ELSE():
            self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

            self.control_stack.append(join_block)
            self.current_block = false_block

            self.visitBlockStatement(ctx.blockStatement(1))

            join_block = self.control_stack.pop()
            # This check guarantees that a false block will not jump to a join
            # while dealing with nested conditionals.
            if self.control_stack and len(self.graph.edges(false_block.nid)) == 0:
                false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)
            elif len(self.control_stack) == 0 and len(self.graph.edges(false_block.nid)) == 0:
                false_block.add(Jump(join_block.label))
                self.graph.add_edge(false_block.nid, join_block.nid)

        # Add the current join to the parent join.
        if self.control_stack:
            join_block.add(Jump(self.control_stack[-1].label))
            self.graph.add_edge(join_block.nid, self.control_stack[-1].nid)

        # self.basic_blocks[self.scope_stack[-1]][self.current_block.nid] = self.current_block
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        self.current_block = join_block

        return NOP()

    def visitWhileStatement(self, ctx: BSParser.WhileStatementContext):
        # Finished with this block.
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        # Insert header block for the conditional.
        header_block = BasicBlock()
        header_label = Label("bsbbw_{}_h".format(header_block.nid))
        self.labels[header_label.name] = header_block.nid
        header_block.add(header_label)
        self.graph.add_node(header_block.nid, function=self.scope_stack[-1], label=header_label.label)
        self.functions[self.scope_stack[-1]]['blocks'][header_block.nid] = header_block

        # We have a directed edge from current block to the header.
        self.graph.add_edge(self.current_block.nid, header_block.nid)
        # The current block jumps to the subsequent header block.
        # self.current_block.add(Jump(header_block.label))

        # The condition goes in the header.
        cond = self.visitParExpression(ctx.parExpression())
        condition = Conditional(cond[0].op, cond[0].left, cond[0].right)
        header_block.add(condition)

        self.control_stack.append(header_block)

        # Set up true block.
        true_block = BasicBlock()
        true_label = Label("bsbbw_{}_t".format(true_block.nid))
        self.labels[true_label.name] = true_block.nid
        true_block.add(true_label)
        self.graph.add_node(true_block.nid, function=self.scope_stack[-1], label=true_label.label)
        self.functions[self.scope_stack[-1]]['blocks'][true_block.nid] = true_block
        condition.true_branch = true_label

        # We have a directed edge from header to true block.
        self.graph.add_edge(header_block.nid, true_block.nid)

        self.current_block = true_block

        self.visitBlockStatement(ctx.blockStatement())

        # The block statement may contain nested conditionals.
        # If so, the current block is the last false block created for the inner-most conditional
        #   otherwise, the current block is the true_block created above.
        # Either way, we can pop the control stack to find where to place the back edge
        #   and immediately make the back edge (from 'current block') to the parent.
        parent_block = self.control_stack.pop()
        self.graph.add_edge(self.current_block.nid, parent_block.nid)
        # self.current_block.add(Jump(parent_block.label))

        # We now deal with the false branch.
        false_block = BasicBlock()

        false_label = Label("bsbbw_{}_f".format(false_block.nid))
        self.labels[false_label.name] = false_block.nid
        false_block.add(false_label)
        condition.false_branch = false_label
        # We are done, so we need to handle the book keeping for
        # Next basic block generation.
        self.graph.add_node(false_block.nid, function=self.scope_stack[-1], label=false_label.label)
        self.graph.add_edge(header_block.nid, false_block.nid)
        self.functions[self.scope_stack[-1]]['blocks'][false_block.nid] = false_block

        # Naively add the edge back to whatever is on the stack.
        # This allows the false node of the while statement to properly jump
        # to where it belongs.  This does add an extra edge that might not
        # need to exist.  If we don't need it (see the crazy restrictive
        # conditional in the visitIfStatement function), then it will be
        # removed.
        # if self.control_stack:
        #     self.graph.add_edge(false_block.nid, self.control_stack[-1].nid)
        #     false_block.add(Jump(self.control_stack[-1].label))

        self.current_block = false_block

        return NOP()

    def visitRepeat(self, ctx: BSParser.RepeatContext):
        # get the (statically defined!) repeat value and add to local symbol table
        value = self.visitLiteral(ctx)
        val = {'name': "REPEAT_{}".format(value), "index": 0,
               'value': value, 'types': ChemTypeResolver.numbers()}

        if 'value' in val.keys() and not self.symbol_table.get_local(val['name']):
            localz = Symbol(val['name'], 'global', ChemTypeResolver.numbers())
            localz.value = Number(val['name'], 1, val['value'])
            self.symbol_table.add_local(localz)

        # finished with this block
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

        # insert header block for the conditional
        header_block = BasicBlock()
        header_label = Label("bsbbr_{}_h".format(header_block.nid))
        self.labels[header_label.name] = header_block.nid
        header_block.add(header_label)
        self.graph.add_node(header_block.nid, function=self.scope_stack[-1], label=header_label.label)
        self.functions[self.scope_stack[-1]]['blocks'][header_block.nid] = header_block
        self.graph.add_edge(self.current_block.nid, header_block.nid)

        zero = self.symbol_table.get_global('CONST_0')
        op = BinaryOp(
            left={'name': val['name'], 'offset': 0, 'size': 1, 'var': self.symbol_table.get_local(val['name'])},
            right={'name': zero.name, 'offset': 0, 'size': 1, 'var': zero},
            op=RelationalOps.GT)
        condition = Conditional(RelationalOps.GT, op.left, op.right)  # Number('Constant_{}'.format(0), 1, 0))
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
        self.graph.add_edge(header_block.nid, true_block.nid)

        self.current_block = true_block
        self.visitBlockStatement(ctx.blockStatement())

        # repeat is translated to a while loop as: while (exp > 0);
        # hence, we update exp by decrementing.
        one = self.symbol_table.get_global('CONST_1')

        ir = Math({'name': val['name'], 'offset': 0, 'size': 1, 'var': self.symbol_table.get_local(val['name'])},
                  {'name': val['name'], 'offset': 0, 'size': 1, 'var': self.symbol_table.get_local(val['name'])},
                  {'name': one.name, 'offset': 0, 'size': 1, 'var': one},
                  BinaryOps.SUBTRACT)

        self.current_block.add(ir)

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

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        args = list()
        for expr in ctx.primary():
            arg = self.visitPrimary(expr)
            var = self.symbol_table.get_symbol(arg['name'], self.scope_stack[-1])
            if arg['index'] == -1 and var.value.size <= 1:
                offset = 0
            else:
                offset = arg['index']
            args.append({'name': var.name, 'offset': offset, 'var': var, 'size': var.value.size})

        return args

    def visitMethodInvocation(self, ctx: BSParser.MethodInvocationContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        deff['var'] = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])
        if deff['var'].value is None: #last ditch effort to give this value a pseudo value
            deff['var'].value = Reagent(deff['name'], 1, 10.0, BSVolume.MICROLITRE)
        if deff['var'].value.size <= 1 and deff['index'] == -1:
            offset = 0
        else:
            offset = deff['index']
        method_name, args = self.visitMethodCall(ctx.methodCall())
        self.current_block.add(
            Call({'name': deff['name'], 'offset': offset}, self.symbol_table.functions[method_name], args))

        # Create the jump to the function.
        jump_location = self.get_entry_block(method_name)
        # Build the graph edge.
        add_cycle(self.graph, [self.current_block.nid, jump_location['nid']])
        #self.graph.add_cycle([self.current_block.nid, jump_location['nid']])
        # self.current_block.add(Jump(jump_location['label']))
        # Sve the block.
        self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block
        # Save this for the return call.
        previous_nid = self.current_block.nid
        # We must create a new block.
        self.current_block = BasicBlock()
        # This is the return call from the return call.
        self.current_block.add(Label('{}_return_{}'.format(method_name, previous_nid)))
        # self.functions[self.scope_stack[-1]]['blocks'][self.current_block.nid] = self.current_block

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        method_name = ctx.IDENTIFIER().__str__()
        args = list()
        if ctx.expressionList():
            args = self.visitExpressionList(ctx.expressionList())
        return method_name, args

    def visitStore(self, ctx: BSParser.StoreContext):
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})
        ir = Store({'name': use['name'], 'offset': use['index'], 'size': use_var.value.size, 'var': use_var.value})
        self.current_block.add(ir)

    def visitNumberAssignment(self, ctx: BSParser.NumberAssignmentContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        value = self.visitLiteral(ctx.literal())
        size = 1 if deff['index'] == -1 else deff['index']
        offset = deff['index'] if deff['index'] != size else -1

        variable = Number(deff['name'], size, value)
        self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).value = variable

        ir = Constant({'name': deff['name'], 'offset': offset, 'size': size, 'var': variable},
                      variable.value)
        self.current_block.add(ir)

        return None

    def visitMath(self, ctx: BSParser.MathContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        deff_var = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])
        deff_offset = 0 if deff['index'] == -1 else deff['index']
        size = 1 if deff['index'] == -1 else deff['index']
        # Has this variable been declared before?
        if deff_var.value is not None:
            self.check_bounds({'name': deff['name'], 'index': deff['index'], 'var': deff_var.value})
            deff_var = deff_var.value
        else:
            deff_var = Number(deff['name'], size)
            self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).value = deff_var

        # Check to see if this is a constant or a variable
        op1 = self.visitPrimary(ctx.primary(0))
        if 'value' in op1.keys():
            op1_var = self.symbol_table.get_global('CONST_{}'.format(op1['value'])).value
        else:
            op1_var = self.symbol_table.get_local(op1['name'], self.scope_stack[-1]).value
        self.check_bounds({'name': op1['name'], 'index': op1['index'], 'var': op1_var})

        # Check to see if this is a constant or a variable
        op2 = self.visitPrimary(ctx.primary(1))
        if 'value' in op2.keys():
            op2_var = self.symbol_table.get_global('CONST_{}'.format(op2['value'])).value
        else:
            op2_var = self.symbol_table.get_local(op2['name'], self.scope_stack[-1]).value
        self.check_bounds({'name': op2['name'], 'index': op2['index'], 'var': op2_var})

        # Set the offsets for everything.
        op1_offset = 0 if op1['index'] == -1 else op1['index']
        op2_offset = 0 if op2['index'] == -1 else op2['index']

        # Grab the operand.
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

        ir = Math({'name': deff['name'], 'offset': deff_offset, 'size': deff_var.size, 'var': deff_var},
                  {'name': op1_var.name, 'offset': op1_offset, 'size': op1_var.size, 'var': op1_var},
                  {'name': op2_var.name, 'offset': op2_offset, 'size': op2_var.size, 'var': op2_var},
                  operand)
        self.current_block.add(ir)

        if deff_var.value is None:
            deff_var.value = Number(deff['name'], value=outcome)

        return None

    def visitMix(self, ctx: BSParser.MixContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())

        # Start of volume parsing
        _volume = []  # A list that holds all the (if any) units parsed.

        v1 = False
        v2 = False
        if len(ctx.unitTracker()) == 0:
            _volume = [10, 10]

        if len(ctx.unitTracker()) == 1:

            pos_unit_tracker = -1
            pos_var_def = []

            for i in range(
                    len(ctx.children)):  # Find the relative position of the unit tracker context and variable contexts

                if type(ctx.children[i]) == BSParser.VariableContext:
                    pos_var_def.append(
                        i)  # Record the position of all variable contexts. There should always and only be two.

                if type(ctx.children[i]) == BSParser.UnitTrackerContext:
                    pos_unit_tracker = i  # Record the position of the unit tracker context. Since this is the case where only one parameter was passed,there should always and only be one instance in this case.

            if min(pos_var_def) > pos_unit_tracker:  # If the unit tracker appears before the first variable definition
                _volume.append(int(ctx.unitTracker()[
                                       0].INTEGER_LITERAL().__str__()))  # Assume that the unit tracker is storing the parameter for the first variable
                _volume.append(10)
                v1 = True

            else:
                _volume.append(10)
                _volume.append(int(ctx.unitTracker()[
                                       0].INTEGER_LITERAL().__str__()))  # If it isn't the first variable's parameter, it must be the second's.
                v2 = True

        if len(ctx.unitTracker()) == 2:
            v1 = True
            v2 = True
            for i in range(2):  # Iterate through the contents of the list returned by unitTracker()
                if type(ctx.unitTracker()[i]) != BSParser.UnitTrackerContext:
                    _volume.append(10)  # Default to 10 if the volume hasn't been explicitly declared
                else:
                    _volume.append(int(ctx.unitTracker()[i].INTEGER_LITERAL().__str__()))

        symbol = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])

        uses = list()
        index = 0
        for fluid in ctx.variable():
            use = self.visitVariable(fluid)
            # if we are dispensing here, then we must create the variable
            # TODO for implicit dispenses, we should check if the deff exists already, if we are to supporting adding
            #   to an indexed variable:
            #   a[4] = dispense aaa has size 4
            #   x[0] = mix aaa with bbb  # x is size one
            #   x[1] = mix aaa with bbb  # x increased to size two
            #     ...... etc.
            if (index == 0 and not v1) or (index == 1 and not v2):
                if use['index'] >= 0:
                    self.check_bounds({'name': use['name'], 'index': use['index'], 'var': self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value})
                    _volume[index] = self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value.value[use['index']].volume['quantity']
                else:
                    _volume[index] = self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value.volume['quantity']
            if (use['name'].startswith("temp_dispense_")):
                if use['index'] == -1 or use['index'] == 0:
                    size = 1
                else:
                    size = use['index']
                self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value = Movable(use['name'],
                                                                                               size=size,
                                                                                               volume=_volume[index])
                use_offset = use['index'] if use['index'] != size else -1
                ir = Dispense({'name': use['name'], 'offset': use_offset, 'size': size,
                               'var': self.symbol_table.get_local(use['name'], self.scope_stack[-1])},
                              {'name': use['name'].split("temp_dispense_")[1], 'offset': 1, 'size': float("inf")})

                if ir.iid in self.symbol_table.get_local(use['name'], self.scope_stack[-1]).volumes:
                    self.symbol_table.get_local(use['name'], self.scope_stack[-1]).volumes[ir.iid].append(_volume[index])
                else:
                    self.symbol_table.get_local(use['name'], self.scope_stack[-1]).volumes[ir.iid] = [_volume[index]]

                self.current_block.add(ir)

            var = self.symbol_table.get_local(use['name'], self.scope_stack[-1]).value
            uses.append({'var': var, 'index': use['index'], 'name': use['name']})
            index += 1
        use_a = uses[0]
        use_b = uses[1]

        # Get the time modifier, should one exist.
        time_meta = None
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            time_meta = TimeConstraint(IRInstruction.MIX, time['quantity'], time['units'])

        # Get the usein time modifier, should one exist.
        usein_meta = None
        if ctx.usein():
            usein_meta = self.visitUsein(ctx.usein())

        if (use_a['index'] == -1 and use_a['var'].size > 1) and (use_b['index'] == -1 and use_b['var'].size > 1):
            if use_a['var'].size != use_b['var'].size:
                raise InvalidOperation("{} is not the same size as {}".format(use_a['var'].name, use_b['var'].name))
            size = use_a['var'].size
        else:
            self.check_bounds(use_a)
            self.check_bounds(use_b)
            size = 1

        if not symbol.value:
            # Update the symbol in the symbol table with the new value
            symbol.value = Movable(deff['name'], size, volume=float(-1))

        ir = Mix({'name': deff['name'], 'offset': deff['index'], 'size': size, 'var': symbol},
                 {'name': use_a['var'].name, 'offset': use_a['index'], 'size': use_a['var'].size, 'var': use_a['var']},
                 {'name': use_b['var'].name, 'offset': use_b['index'], 'size': use_b['var'].size, 'var': use_b['var']})
        if time_meta:
            ir.meta.append(time_meta)
        if usein_meta:
            ir.meta.append(usein_meta)

        self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).volumes[ir.iid] = _volume

        self.current_block.add(ir)

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

        if symbol.value is None:
            symbol.value = Number(deff['name'], use_var.value.size)

        self.check_bounds({'index': use['index'], 'name': use_var.name, 'var': use_var.value})

        ir = Detect({'name': deff['name'], 'offset': use['index'], 'size': symbol.value.size, 'var': symbol.value},
                    {'name': module.name, 'offset': 0, 'size': float("inf"), 'var': module},
                    {'name': use['name'], 'offset': use['index'], 'size': use_var.value.size, 'var': use_var.value})
        if time_meta is not None:
            ir.meta.append(time_meta)
        self.current_block.add(ir)

        return None

    def visitHeat(self, ctx: BSParser.HeatContext):
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        time = None
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())

        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())

        # Get the usein time modifier, should one exist.
        usein_meta = None
        if ctx.usein():
            usein_meta = self.visitUsein(ctx.usein())

        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})

        val = {'name': use['name'], 'offset': use['index'], 'size': use_var.value.size, 'var': use_var}
        ir = Heat(val, val)
        ir.meta.append(TempConstraint(IRInstruction.HEAT, temp['quantity'], temp['units']))
        if time is not None:
            ir.meta.append(TimeConstraint(IRInstruction.HEAT, time['quantity'], time['units']))
        if usein_meta:
            ir.meta.append(usein_meta)
        self.current_block.add(ir)

        return None

    def visitUsein(self, ctx:BSParser.UseinContext):
        time = self.visitTimeIdentifier(ctx.timeIdentifier())
        if ctx.useinType():
            uitype = self.visitUseinType(ctx.useinType())
            return UseIn(time['quantity'], time['units'], uitype)
        return UseIn(time['quantity'], time['units'])

    def visitSle(self, ctx:BSParser.SleContext):
        return UseInType.SLE

    def visitSeq(self, ctx:BSParser.SeqContext):
        return UseInType.SEQ

    def visitSge(self, ctx:BSParser.SgeContext):
        return UseInType.SGE

    def visitFle(self, ctx:BSParser.FleContext):
        return UseInType.FLE

    def visitFeq(self, ctx:BSParser.FeqContext):
        return UseInType.FEQ

    def visitFge(self, ctx:BSParser.FgeContext):
        return UseInType.FGE

    # def visitUseinType(self, ctx:BSParser.UseinTypeContext):
        # return {'uitype': BSParser.symbolicNames[ctx.children[1].symbol.type]}

    def visitSplit(self, ctx: BSParser.SplitContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())
        symbol = self.symbol_table.get_local(deff['name'], self.scope_stack[-1])

        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])
        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})

        offset = 0 if use['index'] == -1 and use_var.value.size == 1 else use['index']
        split_num = int(ctx.INTEGER_LITERAL().__str__())

        ir = Split({'name': deff['name'], 'offset': -1, 'size': split_num, 'var': symbol},
                   {'name': use['name'], 'offset': offset, 'size': use_var.value.size, 'var': use_var}, split_num)
        self.current_block.add(ir)

        if symbol.value is None:
            split_modifier = 1 if use['index'] >= 0 else use_var.value.size
            symbol.value = Movable(deff['name'], size=split_num * split_modifier)

        return None

    def visitDispense(self, ctx: BSParser.DispenseContext):
        deff = self.visitVariableDefinition(ctx.variableDefinition())

        if deff['index'] == -1 or deff['index'] == 0:
            size = 1
        else:
            size = deff['index']

        # Grab the declared volume of the variable and store it
        _volume = 0
        if type(ctx.unitTracker()) != BSParser.UnitTrackerContext:
            _volume = 10  # Default to 10 if the volume hasn't been explicitly declared
        else:
            _volume = deepcopy(int(ctx.unitTracker().INTEGER_LITERAL().__str__()))

        # We don't have to check here, because this is a dispense.

        offset = deff['index'] if deff['index'] != size else -1

        self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).value = Movable(deff['name'],
                                                                                        size=size,
                                                                                        volume=_volume)

        ir = Dispense({'name': deff['name'], 'offset': offset, 'size': size,
                       'var': self.symbol_table.get_local(deff['name'], self.scope_stack[-1])},
                      {'name': ctx.IDENTIFIER().__str__(), 'offset': 1, 'size': float("inf")})

        if ir.iid in self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).volumes:
            self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).volumes[ir.iid].append(_volume)
        else:
            self.symbol_table.get_local(deff['name'], self.scope_stack[-1]).volumes[ir.iid] = [_volume]

        self.current_block.add(ir)
        return None

    def visitDispose(self, ctx: BSParser.DisposeContext):
        use = self.visitVariable(ctx.variable())
        use_var = self.symbol_table.get_local(use['name'], self.scope_stack[-1])

        self.check_bounds({'index': use['index'], 'name': use['name'], 'var': use_var.value})
        ir = Dispose({'name': use['name'], 'offset': use['index'], 'var': use_var.value, 'size': use_var.value.size})
        self.current_block.add(ir)
        return None
