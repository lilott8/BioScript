from compiler.semantics.bs_base_visitor import BSBaseVisitor
from compiler.symbol_table import SymbolTable
from grammar.parsers.python.BSParser import BSParser
from shared.bs_exceptions import InvalidOperation
from shared.bs_exceptions import UndefinedException
from shared.enums.bs_properties import *
from shared.enums.instructions import Instruction


class TargetVisitor(BSBaseVisitor):

    def __init__(self, symbol_table: SymbolTable, name: str):
        self.name = name
        self.compiled = ""
        super().__init__(symbol_table)

    def add(self, code: str):
        self.compiled += code + self.nl

    def print_program(self):
        self.log.warning(self.compiled)

    def visitDetect(self, ctx: BSParser.DetectContext):
        output = "detect("
        module = self.check_identifier(ctx.IDENTIFIER(0).__str__())
        material = self.check_identifier(ctx.IDENTIFIER(1).__str__())
        output += "{}, {}, ".format(module, material)
        time = {}
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            output += "{}".format(time['quantity'])
        else:
            time['quantity'] = 10.0
            time['units'] = BSTime.SECOND
            output += "10.0"

        output += ");"

        is_simd = True if self.symbol_table.get_variable(material).size > 1 else False
        return {'operation': output, 'instruction': Instruction.DETECT,
                'args': {'input': material, 'module': module, 'time': time},
                'variable': self.symbol_table.get_variable(material),
                'size': self.symbol_table.get_variable(material).size, 'is_simd': is_simd}

    def visitSplit(self, ctx: BSParser.SplitContext):
        name = self.check_identifier(ctx.IDENTIFIER().__str__())
        # Split can never be a SIMD operation.
        return {"operation": "split({}, {});".format(name, ctx.INTEGER_LITERAL().__str__()),
                "instruction": Instruction.SPLIT, "size": int(ctx.INTEGER_LITERAL().__str__()),
                'args': {'input': name, "quantity": int(ctx.INTEGER_LITERAL().__str__())},
                'variable': self.symbol_table.get_variable(name), 'is_simd': False}

    def visitDispense(self, ctx: BSParser.DispenseContext):
        """
        Read the comment in visitVariableDeclaration() for further understanding of why
        is_simd = False and size = 1.  In short, the name of the variable in here
        is going to be a global variable and will always be of size = 1
        :param ctx:
        :return:
        """
        name = ctx.IDENTIFIER().__str__()
        return {'operation': "dispense({});".format(name),
                "instruction": Instruction.DISPENSE, 'size': 1,
                'args': {'input': name, 'quantity': 10.0, 'units': BSVolume.MICROLITRE},
                'variable': self.symbol_table.get_variable(name),
                'is_simd': False}

    def visitMethodCall(self, ctx: BSParser.MethodCallContext):
        operation = "{}(".format(ctx.IDENTIFIER().__str__())
        arguments = ""
        method = self.symbol_table.functions[ctx.IDENTIFIER().__str__()]
        if ctx.expressionList():
            operation += "{}".format(self.visitExpressionList(ctx.expressionList()))
            arguments = "{}".format(self.visitExpressionList(ctx.expressionList()))
        operation += ");"
        is_simd = True if method.return_size > 1 else False
        return {'operation': operation, 'instruction': Instruction.METHOD,
                'args': {'args': arguments}, 'size': method.return_size, 'function': method, 'is_simd': is_simd}

    def visitMix(self, ctx: BSParser.MixContext):
        output = "mix("
        inputs = []
        time = {}
        test = set()
        for v in ctx.volumeIdentifier():
            var = self.visit(v)
            inputs.append(var)
            output += "{}, {}, ".format(self.check_identifier(var['variable'].name), var['quantity'])
            if not self.symbol_table.is_global(var['variable']):
                """
                If the variable is global,
                then we can safely assume
                we have an infinite amount.
                """
                test.add(var['variable'].size)
        if len(test) > 1:
            """
            If we are mixing 2 globals, this will be 0.
            Otherwise, if it's > 1, throw an error.
            """
            raise InvalidOperation("Trying to run SIMD on unequal array sizes")
        if len(test) == 0:
            test.add(1)
        if ctx.timeIdentifier():
            time = self.visitTimeIdentifier(ctx.timeIdentifier())
            output += time['quantity']
        else:
            output += "10.0"
            time['quantity'] = 10.0
            time['units'] = BSTime.SECOND
        output += ");"
        is_simd = True if next(iter(test)) > 1 else False
        # This will get the first element of the set "test"
        return {'operation': output, 'instruction': Instruction.MIX,
                'args': {'input': inputs, 'time': time}, 'size': next(iter(test)), 'is_simd': is_simd}

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        if ctx.IDENTIFIER():
            if not self.symbol_table.get_variable(ctx.IDENTIFIER().__str__(), self.scope_stack[-1]):
                raise UndefinedException("Undeclared variable: {}".format(ctx.IDENTIFIER().__str__()))
            return ctx.IDENTIFIER().__str__()
        elif ctx.literal():
            return self.visitLiteral(ctx.literal())
        else:
            return self.visitExpression(ctx.expression())

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        if ctx.INTEGER_LITERAL():
            return ctx.INTEGER_LITERAL().__str__()
        elif ctx.BOOL_LITERAL():
            return ctx.BOOL_LITERAL().__str__()
        elif ctx.FLOAT_LITERAL():
            return ctx.FLOAT_LITERAL().__str__()
        else:
            return ctx.STRING_LITERAL().__str__()

    def process_simd(self, lhs: str, op: Instruction, args: dict) -> dict:
        raise NotImplementedError

    def process_sisd(self, lhs: str, op: Instruction, args: dict) -> dict:
        raise NotImplementedError
