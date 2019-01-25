from bioscript.visitors.targets.target_visitor import TargetVisitor
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import *
from shared.enums.instructions import Instruction
from shared.enums.instructions import InstructionSet
from shared.tree_node import TreeNode


class PuddleVisitor(TargetVisitor):

    def __init__(self, symbol_table):
        super().__init__(symbol_table, "PuddleVisitor")
        self.tab_count = 0
        self.tab = ""

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
        self.scope_stack.append("main")

        output = "from puddle import mk_session, project_path {}".format(self.nl)

        if ctx.functionDeclaration():
            output += self.nl
            for func in ctx.functionDeclaration():
                output += "{}{}{}".format(self.visitFunctionDeclaration(func), self.nl, self.nl)

        self.symbol_table.current_scope = self.symbol_table.scope_map['main']
        output += 'arch_path = project_path("{}"){}'.format('PUT SOMETHING HERE', self.nl)
        output += 'with mk_session(arch_path) as session:{}'.format(self.nl)

        # output += "{}".format(self.visitManifestDeclaration(ctx.manifestDeclaration()))

        for i in ctx.statements():
            output += self.visitStatements(i)

        self.compiled = self.nl + output

    def visitModuleDeclaration(self, ctx: BSParser.ModuleDeclarationContext):
        return super().visitModuleDeclaration(ctx)

    def visitManifestDeclaration(self, ctx: BSParser.ManifestDeclarationContext):
        output = ""
        for manifest in ctx.IDENTIFIER():
            name = manifest.__str__()
            output += '{}{} = session.input(location=(), volume=1000000.0, dimensions=(1,1)){}'.format(self.tab, name,
                                                                                                       self.nl)
        return output

    def visitStationaryDeclaration(self, ctx: BSParser.StationaryDeclarationContext):
        return super().visitStationaryDeclaration(ctx)

    def visitFunctionDeclaration(self, ctx: BSParser.FunctionDeclarationContext):
        name = ctx.IDENTIFIER().__str__()
        func = self.symbol_table.functions[name]
        output = ""

        self.scope_stack.append(name)
        self.symbol_table.current_scope = self.symbol_table.scope_map[name]

        output += "{}def {} (".format(self.tab, name)
        if func.args:
            for arg in func.args:
                output += "{}, ".format(arg.name)
            output = output[:-2]
        output += "):{}".format(self.nl)

        self.increment_tab()
        for statement in ctx.statements():
            output += self.visitStatements(statement)

        output += "{}return {}{}".format(self.tab, self.visitReturnStatement(ctx.returnStatement()), self.nl)
        self.decrement_tab()

        self.add(output)
        self.scope_stack.pop()
        return output

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
            output += self.visitStatements(x)
            output += "{}session._flush(){}".format(self.tab, self.nl)
        return output

    def visitStatements(self, ctx: BSParser.StatementsContext):
        return "{}{}{}".format(self.tab, self.visitChildren(ctx), self.nl)

    def visitIfStatement(self, ctx: BSParser.IfStatementContext):
        output = ""
        # Build the if condition....
        condition = self.visitParExpression(ctx.parExpression())
        output += "if {}:{}".format(condition, self.nl)
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

    def visitHeat(self, ctx: BSParser.HeatContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        temp = self.visitTemperatureIdentifier(ctx.temperatureIdentifier())
        time = self.visitTimeIdentifier(ctx.timeIdentifier())

        output = ""
        if variable.size > 1:
            """
            This is a SIMD operation.
            """
            for x in range(0, variable.size):
                output += "{}{}[{}] = session.heat({}[{}], {}){}".format(
                    self.tab, variable.name, x, variable.name, x, temp['quantity'], self.nl)
                inputs = []
                outputs = []
                # name = "{}{}".format(variable.name, x)
                # inputs.append(MFSimVarBuilder.build_general_input(Variable(name, set())))
                # inputs.append(MFSimVarBuilder.build_temperature_property(temp['quantity'], temp['units']))
                # # Add time property.
                # if ctx.timeIdentifier():
                #     inputs.append(MFSimVarBuilder.build_time_property(time['quantity'], time['units']))
                # output.append(MFSimVarBuilder.build_operation('HEAT', 'getInstructionId()', 'HEAT', inputs, outputs))
        else:
            """
            This is not a SIMD operation.
            """
            output += "{} = session.heat({},temp={},seconds={})".format(
                variable.name, variable.name, temp['quantity'], time['quantity'])
        return output

    def visitDispose(self, ctx: BSParser.DisposeContext):
        variable = self.symbol_table.get_variable(ctx.IDENTIFIER().__str__())
        output = ""
        if variable.size > 1:
            """
            This is a SIMD operation.
            """
            for x in range(0, variable.size):
                output += "{}output({}[{}]){}".format(self.tab, variable.name, x, self.nl)
        else:
            """
            This is not a SIMD operation.
            """
            output += "output({}){}".format(variable.name, self.nl)
        return output

    def visitParExpression(self, ctx: BSParser.ParExpressionContext):
        return "({})".format(self.visitExpression(ctx.expression()))

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        return super().visitMethodCall(ctx)

    def visitExpressionList(self, ctx: BSParser.ExpressionListContext):
        return super().visitExpressionList(ctx)

    def visitVariableDeclaration(self, ctx: BSParser.VariableDeclarationContext):
        return self.visitChildren(ctx)

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        name = ctx.IDENTIFIER().__str__()
        # Get the inputs...
        op = self.visitChildren(ctx)

        output = ""
        if 'instruction' in op:
            if op['instruction'] not in InstructionSet.instructions:
                raise InvalidOperation("Unknown instruction: {}".format(op['op'].name))
            if op['instruction'] == Instruction.DISPENSE:
                """
                This has to happen here; a = dispense bbb will always give us a size = 1 and is_simd = False.
                This is because in the visitDispenseStatement() parsing, the variable that will determine
                is_simd will be 'bbb', a global variable of size = 1.  Thus is_simd will always be False.
                In order for Dispense to know if it's a SIMD operation, we must know to what variable
                the dispense is occurring -- as that will tell us if it's a SIMD operation or not.
                """
                op['is_simd'] = True if self.symbol_table.get_variable(name).size > 1 else False
                op['size'] = self.symbol_table.get_variable(name).size
            if op['is_simd']:
                output = self.process_simd(name, op['instruction'], op)
            else:
                output = self.process_sisd(name, op['instruction'], op)
        else:
            output += "{}{} = {}".format(self.tab, name, op)
        return output

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> dict:
        output = ""

        if op == Instruction.SPLIT:
            self.log.error("Not doing anything with split, right now.")
            pass
        elif op == Instruction.MIX:
            mixes = "{} = list(){}".format(lhs, self.nl)
            dispenses = ""
            input_1 = args['args']['input'][0]['variable']
            input_2 = args['args']['input'][1]['variable']
            """
            Only one of the variables will be a global.  
            If no variables are global, then both must be arrays.
            If they aren't then it would be a sisd-instruction.
            """
            if input_1.is_global:
                for x in range(0, args['size']):
                    dispenses += self.get_input("{}_{}".format(input_1.name, x), input_1.name, 10.0)
                    mixes += "{}{}.append(session.mix({}[{}], {}_{})){}".format(self.tab, lhs, input_2.name, x,
                                                                                input_1.name, x, self.nl)
            elif input_2.is_global:
                for x in range(0, args['size']):
                    dispenses += self.get_input("{}_{}".format(input_2.name, x), input_2.name, 10.0)
                    mixes += "{}{}.append(session.mix({}[{}], {}_{})){}".format(self.tab, lhs, input_1.name, x,
                                                                                input_2.name, x, self.nl)
            else:
                for x in range(0, args['size']):
                    mixes += "{}{}.append(session.mix({}[{}], {}[{}])){}".format(self.tab, lhs, input_1.name, x,
                                                                                 input_2.name, x, self.nl)
            output += dispenses
            output += mixes
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            self.log.critical("Not sure if Puddle supports detection yet...")
            output += "{}{} = list(){}".format(self.tab, lhs, self.nl)
            for x in range(0, args['size']):
                output += "{}{}[{}] = session.detect({}[{}], sensor={}){}".format(self.tab, lhs, x,
                                                                                  args['args']['input'], x,
                                                                                  args['args']['module'], self.nl)
            pass
        elif op == Instruction.METHOD:
            self.log.critical("Alpha-convert this trash!")
            pass
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            output += "{}{} = list(){}".format(self.tab, lhs, self.nl)
            for x in range(0, args['size']):
                output += '{}{}[{}] = session.input({}, location=(), volume=1000000.0, dimensions=(1,1)){}'.format(
                    self.tab, lhs, x, args['args']['input'], self.nl)
        return output

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> str:
        output = ""
        if op == Instruction.SPLIT:
            output += self.build_split(lhs, args['args']['input'], args['args']['quantity'])
            #output += "std::vector<mat> {} = split({}, {});".format(
            #    lhs, args['args']['input'], args['args']['quantity'])
        elif op == Instruction.MIX:
            mixes = ""
            for x in args['args']['input']:
                mixes += "{}, ".format(x['variable'].name)
            # Note the comma between ({} {}) is appended to the first {}!
            output += "{} = mix({})".format(lhs, mixes[:-2])
        elif op == Instruction.HEAT:
            # Heat is an independent statement.  Meaning it is resolved in the visitHeatStatement()
            pass
        elif op == Instruction.DETECT:
            # args['args']['time']['quantity'] is the time component.
            output += "{} = detect({}, {})".format(
                lhs, args['args']['module'], args['args']['input'])
        elif op == Instruction.METHOD:
            output += "{} = {}({})".format(lhs, args['function'].name, args['args']['args'])
            # raise InvalidOperation("Not implemented yet")
        elif op == Instruction.DISPOSE:
            # Dispose is an independent statement.  Meaning it is resolved in the visitDisposeStatement()
            pass
        elif op == Instruction.DISPENSE:
            output += self.get_input(lhs, args['args']['input'], args['args']['quantity'])
        # output += "session._flush(){}".format(self.nl)
        return output

    def build_split(self, output_var, input_var, size):
        output = "{} = list(){}".format(output_var, self.nl)
        quantity = PuddleVisitor.get_exponent(size)
        node = TreeNode(-1)
        nodes = PuddleVisitor.build_tree(node, quantity['quantity'])
        for x in range(0, len(nodes)):
            previous_input = input_var
            if x == 0:
                """
                This handles the initial split.
                """
                output_a = "{}_{}".format(output_var, 1)
                output_b = "{}_{}".format(output_var, 2)
                output += "{}({},{}) = sessions.split({}){}".format(self.tab, output_a, output_b,
                                                                    previous_input, self.nl)
            else:
                """
                These are the intermediary levels of the tree (1-(n-1)).
                """
                previous_input = "{}_{}".format(output_var, nodes[x]['input'])
                output_a = "{}_{}".format(output_var, nodes[x]['output'][0])
                output_b = "{}_{}".format(output_var, nodes[x]['output'][1])
                output += "{}({},{}) = sessions.split({}){}".format(self.tab, output_a, output_b,
                                                                    previous_input, self.nl)

            if (x == (len(nodes) - quantity['exponent']) - 1 and len(nodes) > 3) or x >= len(nodes) - quantity[
                'exponent']:
                """
                Only append the last level of the tree to the list.
                """
                output += "{}{}.append({}){}".format(self.tab, output_var, output_a, self.nl)
                output += "{}{}.append({}){}".format(self.tab, output_var, output_b, self.nl)
        return output

    @staticmethod
    def build_tree(root: TreeNode, quantity: int):
        x = 1
        queue = [root]
        while x <= quantity:
            if queue[0].left is not None and queue[0].right is not None:
                queue.pop(0)
            node = TreeNode(x)
            if x % 2 == 0:
                queue[0].right = node
            else:
                queue[0].left = node
            queue.append(node)
            x += 1
        return PuddleVisitor.build_splits(root)

    @staticmethod
    def build_splits(root: TreeNode) -> list:
        queue = [root]
        splits = list()
        while queue:
            current = queue.pop(0)
            if current.left and current.right:
                splits.append({'input': current.value, 'output': [current.left.value, current.right.value]})

            if current.left:
                queue.append(current.left)
            if current.right:
                queue.append(current.right)

        return splits

    @staticmethod
    def get_exponent(a: int) -> dict:
        x = 1
        count = 0
        total = 0
        while x < a:
            x *= 2
            count += 1
            total += x
        return {"exponent": count, "quantity": total}

    def get_input(self, out_var: str, in_var: str, volume: float = 10.0) -> str:
        return "{} = session.input({}, volume={}){}".format(out_var, in_var, volume, self.nl)
