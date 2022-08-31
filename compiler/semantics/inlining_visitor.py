import copy

from chemicals.chemtypes import ChemTypeResolver, ChemTypes
from chemicals.identifier import Identifier
from compiler.data_structures.variable import Symbol, Number
from grammar.parsers.python.BSParser import BSParser
from grammar.parsers.python.BSLexer import BSLexer
from shared.bs_exceptions import UndefinedVariable, UndefinedFunction, UnsupportedOperation
from .bs_base_visitor import BSBaseVisitor
import os
from antlr4.tree.Tree import TerminalNodeImpl
from antlr4 import InputStream, CommonTokenStream
from antlr4.TokenStreamRewriter import TokenStreamRewriter


class InliningVisitor(BSBaseVisitor):

    def __init__(self, symbol_table, identifier: Identifier, rewriter: TokenStreamRewriter):
        super().__init__(symbol_table, "InliningVisitor", identifier)
        # set of function names that have been checked off
        self.rewriter = rewriter
        self.completed = set()
        self.functions = dict()  # func name to dict of ['statements'] and ['args']
        self.alpha_map = dict()

    def visitProgram(self, ctx: BSParser.ProgramContext):

        # want to update all methodInvocation statements
        #  to be inlined versions of the methodInvocation.

        # to do so, we need to:
        #   (1) make sure methodsDeclarations have been inlined, themselves
        #   (2) for each methodInvocation, perform alpha conversion and inline statements in ctx

        # (1)
        self.visitFunctions(ctx.functions())

        # remove functions from Programcontext

        for i, check in enumerate(ctx.children):
            if isinstance(check, BSParser.FunctionsContext):
                del ctx.children[i]
                break

        # (2), starting at main
        self.inlineHelper(ctx)

    def inlineHelper(self, ctx):
        # for main
        i = 0
        while i < len(ctx.children) and not isinstance(ctx.children[i], BSParser.StatementsContext):
            i += 1

        # at the ith child, which is a statement; will not change ctx.children[:i]
        # for each statement child, check if it's a method call, and replace it with alpha-converted block of statements
        while i < len(ctx.children):
            if isinstance(ctx.children[i], BSParser.ReturnStatementContext):
                # TODO see note below in visitMethodInvocation re: return statements
                return
            elif isinstance(ctx.children[i], TerminalNodeImpl):
                # EOF
                return
            elif ctx.children[i].methodInvocation():
                self.log.debug(f"Method call discovered, inlining at child {i}")
                new_instr = self.visitMethodInvocation(ctx.children[i].methodInvocation())
                del ctx.children[i]
                ctx.children[i:i] = new_instr
                i += len(new_instr)
            else:
                i += 1

    def visitMethodInvocation(self, ctx:BSParser.MethodInvocationContext):
        # this should return a list of statements that have been alpha converted
        func_name, params = self.visitMethodCall(ctx.methodCall())
        self.log.debug(f"inlining {func_name}")
        if func_name not in self.completed:
            # make sure func def is ready for inlining, by looking through statements
            self.log.warning("have not inlined this one!")
            self.inlineHelper(self.functions[func_name]['statements'][0].parentCtx)
            # for statement in self.functions[func_name]:
            #     if isinstance(statement, BSParser.ReturnStatementContext):
            #         self.inlineHelper(statement)
            #     elif statement.methodInvocation():
            #         self.inlineHelper(statement.parentCtx)
            self.completed.add(func_name)
            self.functions[func_name]['statements'] = self.functions[func_name]['statements'][0].parentCtx.statements()
            pass
        formal_params = self.functions[func_name]['args']

        # verify we can map appropriately
        assert len(params) == len(formal_params), f"Call to {func_name} has incorrect number of arguments. Could not match {params} to {formal_params}."

        # for renaming
        self.alpha_map = dict(zip(formal_params, params))

        # now, step through statement by statement, and rename uses as necessary
        new_block = list()
        for statement in self.functions[func_name]['statements']:
            new_statement = copy.copy(statement)
            # TODO need to implement different visitors for each appropriate context.
            #  Contexts that use "variable"s at their head can call visit_vars.
            #  For others (primaries, numericAlias, ifStatements, etc.), a similar approach can be used.
            #  For now, we send everything to visit_vars, as it covers most of our use cases.
            if isinstance(new_statement, BSParser.ReturnStatementContext):
                # TODO -- need to figure out what to do with return statements.
                #  typically, they'll return a primary, such that the caller is setting a variable to this primary
                #       i.e., x = foo(...) {... return y; } means x = y
                #  but we don't do aliasing like this, so we need some other means of renaming
                #  perhaps a good approach would be to visit return statements first, to see what var is being returned
                #  then, at each place the the ret var is def'd within the function, just set it to the caller's assignment name
                #  so x = foo(..) {.. y = ...; return y; }
                #   can discard "return y;" and change y -> x.
                pass
            else:
                self.visit_vars(new_statement.children[0])
            # self.visit(new_statement)

            new_block.append(new_statement)

        return new_block

    def visit_vars(self, ctx):
        for i, tok in enumerate(ctx.children):
            if isinstance(tok, BSParser.VariableContext):
                # we're dealing with a use of a param, need to convert
                if ctx.children[i].IDENTIFIER().__str__() in self.alpha_map:
                    ctx.children[i].children[0] = BSParser(CommonTokenStream(BSLexer(InputStream(self.alpha_map[ctx.children[i].IDENTIFIER().__str__()]['name'])))).variable().children[0]

    def visitMix(self, ctx:BSParser.MixContext):
        self.visit_vars(ctx)

    def visitDetect(self, ctx:BSParser.DetectContext):
        self.visit_vars(ctx)

    def visitMethodCall(self, ctx:BSParser.MethodCallContext):
        # name, parameter list
        return ctx.IDENTIFIER().__str__(), self.visitExpressionList(ctx.expressionList())

    def visitExpressionList(self, ctx:BSParser.ExpressionListContext):
        params = list()
        for child in ctx.children:
            param = self.visit(child)
            if param is not None:
                params.append(param)
        return params

    def visitFunctionDeclaration(self, ctx:BSParser.FunctionDeclarationContext):
        # returns true if parameter list has function call
        name = ctx.IDENTIFIER().__str__()
        self.functions[name] = dict()
        self.functions[name]['statements'] = ctx.statements()
        self.functions[name]['statements'].append(ctx.returnStatement())

        self.functions[name]['args'] = list()
        for param in ctx.formalParameters().children[1].formalParameter():
            self.functions[name]['args'].append(param.children[0].symbol.text)

        if self.visitFormalParameters(ctx.formalParameters()):
            return

        for statement in ctx.statements():
            if statement.methodInvocation():
                return

        self.completed.add(name)

    def visitFormalParameters(self, ctx:BSParser.FormalParametersContext):
        for param in ctx.formalParameterList().children:
            if isinstance(param, BSParser.MethodInvocationContext):
                # TODO -- build out inlining when formal parameters contains methodcall(s)
                return True
        return False
