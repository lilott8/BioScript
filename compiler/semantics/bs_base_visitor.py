import colorlog

from compiler.bs_ir import *
from compiler.symbol_table.scope import Scope
from grammar.parsers.python.BSParser import BSParser
from grammar.parsers.python.BSParserVisitor import BSParserVisitor
from shared.bs_exceptions import *
from shared.helpers import *


class BSBaseVisitor(BSParserVisitor):

    def __init__(self, symbol_table, name="BaseVisitor"):
        super().__init__()
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = Config.getInstance(None)
        self.visitor_name = name
        # The identifier to use.
        self.identifier = get_identifier(self.config.identify)
        # The combiner to use.
        self.combiner = get_combiner(self.config.combine)
        # Name of global scope
        self.global_scope = "global"
        # The current symbol table
        self.symbol_table = symbol_table
        self.nl = "\n"
        # Manages the scopes that we are in.
        self.scope_stack = list()
        # Manages the renamed variables
        self.rename_counter = dict()
        # This *should* be moved into the LLVM target...
        self.keywords = ("alignas", "alignof", "and", "and_eq", "asm", "atomic_cancel", "atomic_commit",
                         "atomic_noexcept", "auto", "bitand", "bitor", "bool", "break", "case", "catch", "char",
                         "char16_t", "char32_t", "class", "compl", "concept", "const", "constexpr", "const_cast",
                         "continue", "co_await", "co_return", "co_yield", "decltype", "default", "delete", "do",
                         "double", "dynamic_cast", "else", "enum", "explicit", "export", "extern", "false", "float",
                         "for", "friend", "goto", "if", "import", "inline", "int", "long", "module", "mutable",
                         "namespace", "new", "noexcept", "not", "not_eq", "nullptr", "operator", "or", "or_eq",
                         "private", "protected", "public", "reflexpr", "register", "reinterpret_cast", "requires",
                         "return", "short", "signed", "sizeof", "static", "static_assert", "static_cast", "struct",
                         "switch", "synchronized", "template", "this", "thread_local", "throw", "true", "try",
                         "typedef", "typeid", "typename", "union", "unsigned", "using", "virtual", "void", "volatile",
                         "wchar_t", "while", "xor", "xor_eq")

    def get_renamed_var(self, name: str):
        """
        Gets a variable from the counter table.
        :param name: Variable to get rename for.
        :return: Renamed variable.
        """
        if name not in self.rename_counter:
            self.rename_counter[name] = 1
            return name
        else:
            return "{}{}".format(name, self.rename_counter[name])

    def increment_rename_var(self, name: str):
        """
        Increment the variable counter for the given name.
        :param name: Name to increment counter.
        :return: The name of the renamed variable.
        """
        if name not in self.rename_counter:
            self.rename_counter[name] = 1
            return name
        else:
            self.rename_counter[name] += 1
            return "{}{}".format(name, self.rename_counter[name])

    def visitVolumeIdentifier(self, ctx: BSParser.VolumeIdentifierContext) -> dict:
        quantity = 10.0
        units = BSVolume.MICROLITRE
        name = ctx.IDENTIFIER().__str__()
        if ctx.VOLUME_NUMBER():
            x = self.split_number_from_unit(ctx.VOLUME_NUMBER().__str__())
            units = BSVolume.get_from_string(x['units'])
            quantity = units.normalize(x['quantity'])
        return {'quantity': quantity, 'units': units,
                'variable': self.symbol_table.get_variable(name, self.scope_stack[-1])}

    def visitTimeIdentifier(self, ctx: BSParser.TimeIdentifierContext) -> dict:
        quantity = 10.0
        units = BSTime.SECOND
        if ctx:
            x = self.split_number_from_unit(ctx.TIME_NUMBER().__str__())
            units = BSTime.get_from_string(x['units'])
            quantity = units.normalize(x['quantity'])
        return {'quantity': quantity, 'units': BSTime.SECOND, 'preserved_units': units}

    def visitTemperatureIdentifier(self, ctx: BSParser.TemperatureIdentifierContext) -> dict:
        x = self.split_number_from_unit(ctx.TEMP_NUMBER().__str__())
        units = BSTemperature.get_from_string(x['units'])
        quantity = units.normalize(x['quantity'])
        return {'quantity': quantity, 'units': BSTemperature.CELSIUS, 'preserved_units': units}

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

    def visitExpression(self, ctx: BSParser.ExpressionContext):
        if ctx.primary():
            return self.visitPrimary(ctx.primary())
        else:
            exp1 = self.visitExpression(ctx.expression(0))
            exp2 = self.visitExpression(ctx.expression(1))
            if ctx.MULTIPLY():
                op = BinaryOps.MULTIPLE
            elif ctx.DIVIDE():
                op = BinaryOps.DIVIDE
            elif ctx.ADDITION():
                op = BinaryOps.ADD
            elif ctx.SUBTRACT():
                op = BinaryOps.SUBTRACT
            elif ctx.AND():
                op = BinaryOps.AND
            elif ctx.EQUALITY():
                op = RelationalOps.EQUAL
            elif ctx.GT():
                op = RelationalOps.GT
            elif ctx.GTE():
                op = RelationalOps.GTE
            elif ctx.LT():
                op = RelationalOps.LT
            elif ctx.LTE():
                op = RelationalOps.LTE
            elif ctx.NOTEQUAL():
                op = RelationalOps.NE
            elif ctx.OR():
                op = BinaryOps.OR
            else:
                op = RelationalOps.EQUAL

            if ctx.LBRACKET():
                """
                In this context, exp1 will *always* hold the variable name.
                So we can check to make sure that exp1 is the appropriate size,
                Given exp2 as the index. 
                """
                variable = self.symbol_table.get_variable(exp1)
                if int(exp2) > variable.size - 1 and int(exp2) >= 0:
                    raise InvalidOperation("Out of bounds index: {}[{}], where {} is of size: {}".format(
                        exp1, exp2, exp1, variable.size))
                output = "{}[{}]".format(exp1, exp2)
            else:
                output = {"exp1": exp1, "exp2": exp2, "op": op}

            return output

    def check_identifier(self, name):
        if name in self.keywords:
            return "{}{}".format(name, name)
        else:
            return name

    @staticmethod
    def get_safe_name(name: str) -> str:
        """
        Unified manner to create program-safe names
        :param name: Name of unsafe variable.
        :return: Safe name.
        """
        return name.replace(" ", "_").replace("-", "_")

    def split_number_from_unit(self, text) -> dict:
        """
        Splits the number and units: 10mL => (10, "mL").
        :param text: Input text for splitting.
        :return: Dictionary of necessary output.
        """
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
        return {'quantity': float(temp_float), 'units': temp_unit}

    def get_scope(self, name) -> Scope:
        """
        Get the scope.
        :param name: name of scope.
        :return: Scope object associated with the name.
        """
        if name not in self.symbol_table.scope_map:
            scope = Scope(name)
            self.symbol_table.scope_map[name] = scope
            return scope
        else:
            return self.symbol_table.scope_map[name]

    @staticmethod
    def is_number(num):
        """
        Simple check to determine if input is a number.
        :param num: Input string.
        :return: Boolean determining if a string is a number.
        """
        try:
            float(num)
            return True
        except ValueError:
            return False
