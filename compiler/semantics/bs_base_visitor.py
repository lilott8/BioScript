from abc import ABCMeta
from typing import Set, Dict

import colorlog

import compiler.data_structures.symbol_table as st
from chemicals.chemtypes import ChemTypeResolver, ChemTypes
from chemicals.identifier import Identifier, NaiveIdentifier
from compiler.data_structures.properties import BSTime, BSTemperature
from compiler.data_structures.scope import Scope
from compiler.data_structures.variable import Number
from grammar.parsers.python.BSParser import BSParser
from grammar.parsers.python.BSParserVisitor import BSParserVisitor


class BSBaseVisitor(BSParserVisitor, metaclass=ABCMeta):

    def __init__(self, symbol_table: st.SymbolTable, name="BaseVisitor", identifier: Identifier = NaiveIdentifier()):
        super().__init__()
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.visitor_name = name
        # The current symbol table
        self.symbol_table = symbol_table
        self.nl = "\n"
        # Manages the scopes that we are in.
        self.scope_stack = list()
        self.const = 'CONST_'
        self.identifier = identifier

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

    def visitVariableDefinition(self, ctx: BSParser.VariableDefinitionContext):
        var = self.visitVariable(ctx.variable())
        if ctx.unionType():
            var['types'] = self.visitUnionType(ctx.unionType())
        return var

    def visitVariable(self, ctx: BSParser.VariableContext):
        """
        Gets the variable to which the statement will be assigned.
        If it's -1, the statement uses the whole array.  Which means
        there must be a check to see if the size of the input arrays
        are equal.
        :param ctx: context of the visitor.
        :return: Dictionary that holds the index and the name of the variable to be assigned.
        """
        # If it's -1, it means there wasn't anything given,
        # so use all the elements of the variable available.
        index = -1 if not ctx.INTEGER_LITERAL() else int(ctx.INTEGER_LITERAL().__str__())
        # Array_ref is context specific, something visitVariable cannot infer.
        # Either it is the size of the element or the index.
        # In something like a dispense, it's a size; if it's a mix, it's an index.
        return {"name": ctx.IDENTIFIER().__str__(), "index": index, 'types': {ChemTypes.UNKNOWN}}

    def visitPrimary(self, ctx: BSParser.PrimaryContext):
        if ctx.variable():
            primary = self.visitVariable(ctx.variable())
        else:
            value = self.visitLiteral(ctx.literal())
            # It's a constant, thus, the size must be 1 and index 0.
            primary = {'name': "{}{}".format(self.const, value), "index": 0,
                       'value': value, 'types': ChemTypeResolver.numbers()}
        return primary

    def visitLiteral(self, ctx: BSParser.LiteralContext):
        if ctx.INTEGER_LITERAL():
            return int(ctx.INTEGER_LITERAL().__str__())
        elif ctx.BOOL_LITERAL():
            return bool(ctx.BOOL_LITERAL().__str__())
        elif ctx.FLOAT_LITERAL():
            return float(ctx.FLOAT_LITERAL().__str__())
        else:
            return ctx.STRING_LITERAL().__str__()

    def visitUnionType(self, ctx: BSParser.UnionTypeContext):
        return self.visitTypesList(ctx.typesList())

    def visitTypesList(self, ctx: BSParser.TypesListContext):
        types = set()
        for t in ctx.typeType():
            types.add(self.visitTypeType(t))
        return types

    def visitTypeType(self, ctx: BSParser.TypeTypeContext):
        if ctx.primitiveType():
            return ChemTypeResolver.string_to_type(self.visitPrimitiveType(ctx.primitiveType()))
        else:
            return self.visitChemicalType(ctx.chemicalType())

    def visitPrimitiveType(self, ctx: BSParser.PrimitiveTypeContext):
        if ctx.MAT():
            return "MAT"
        elif ctx.REAL():
            return "REAL"
        elif ctx.NAT():
            return "NAT"
        elif ctx.BOOL():
            return "NAT"
        else:
            return "MAT"

    def visitChemicalType(self, ctx: BSParser.ChemicalTypeContext):
        try:
            value = ChemTypes(int(ctx.INTEGER_LITERAL().__str__()))
        except ValueError:
            self.log.warning(ctx.INTEGER_LITERAL().__str__() + " has no associated ChemType.  Assigning type UNKNOWN.")
            value = ChemTypes.UNKNOWN
        return value

    # def visitExpression(self, ctx: BSParser.ExpressionContext):
    #     if ctx.primary():
    #         return self.visitPrimary(ctx.primary())
    #     else:
    #         exp1 = self.visitExpression(ctx.expression(0))
    #         exp2 = self.visitExpression(ctx.expression(1))
    #         if ctx.MULTIPLY():
    #             op = BinaryOps.MULTIPLE
    #         elif ctx.DIVIDE():
    #             op = BinaryOps.DIVIDE
    #         elif ctx.ADDITION():
    #             op = BinaryOps.ADD
    #         elif ctx.SUBTRACT():
    #             op = BinaryOps.SUBTRACT
    #         elif ctx.AND():
    #             op = BinaryOps.AND
    #         elif ctx.EQUALITY():
    #             op = RelationalOps.EQUALITY
    #         elif ctx.GT():
    #             op = RelationalOps.GT
    #         elif ctx.GTE():
    #             op = RelationalOps.GTE
    #         elif ctx.LT():
    #             op = RelationalOps.LT
    #         elif ctx.LTE():
    #             op = RelationalOps.LTE
    #         elif ctx.NOTEQUAL():
    #             op = RelationalOps.NE
    #         elif ctx.OR():
    #             op = BinaryOps.OR
    #         else:
    #             op = RelationalOps.EQUALITY
    #
    #         if ctx.LBRACKET():
    #             """
    #             In this context, exp1 will *always* hold the variable name.
    #             So we can check to make sure that exp1 is the appropriate size,
    #             Given exp2 as the index.
    #             """
    #             variable = self.symbol_table.get_variable(exp1)
    #             if int(exp2) > variable.size - 1 and int(exp2) >= 0:
    #                 raise InvalidOperation("Out of bounds index: {}[{}], where {} is of size: {}".format(
    #                     exp1, exp2, exp1, variable.size))
    #             output = "{}[{}]".format(exp1, exp2)
    #         else:
    #             if not self.is_number(exp1):
    #                 exp1 = self.symbol_table.get_local(exp1, self.scope_stack[-1])
    #             if not self.is_number(exp2):
    #                 exp2 = self.symbol_table.get_local(exp2, self.scope_stack[-1])
    #             output = {"exp1": exp1, "exp2": exp2, "op": op}
    #
    #         return output

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

    def resolve_types(self, var: Dict, *argv) -> Set:
        """
        Build the typing information for a variable.
        :param var: The variable needing typing information.
        :return: Set of types.
        """
        if ChemTypes.UNKNOWN in var['types'] and len(var['types']) == 1:
            types = self.identifier.identify(var['name'], var['types'])
            if ChemTypes.UNKNOWN in types:
                types.remove(ChemTypes.UNKNOWN)
            return types
        elif ChemTypes.UNKNOWN in var['types'] and len(var['types']) > 1:
            var['types'].remove(ChemTypes.UNKNOWN)
            return var['types']
        else:
            return var['types']

    @staticmethod
    def is_number(num):
        """
        Simple check to determine if input is a number.
        :param num: Input string.
        :return: Boolean determining if a string is a number.
        """
        try:
            if isinstance(num, Number):
                return False
            float(num)
            return True
        except ValueError:
            return False
