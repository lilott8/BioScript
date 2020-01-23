
import pytest
from antlr4 import *

from compiler.config.compiler_cli import CompilerCLI
from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser


@pytest.fixture(scope="function")
def get_visitor():
    # This allows us to accept arguments to the fixture.
    def _filename(filename: str):
        file_stream = FileStream(filename)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        return parser.program()

    return _filename


@pytest.fixture(scope="function")
def get_config():
    def _get_config(args: str):
        if not args:
            args = "-t ir -d -i TEST_FILE"
        cli = CompilerCLI(args)
        return cli.config

    return _get_config



@pytest.fixture(scope="function")
def get_visitor():
    # This allows us to accept arguments to the fixture.
    def _filename(filename: str):
        file_stream = FileStream(filename)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        return parser.program()

    return _filename


@pytest.fixture(scope="function")
def get_config():
    def _get_config(args: str):
        if not args:
            args = "-t ir -d -i TEST_FILE"
        cli = CompilerCLI(args)
        return cli.config

    return _get_config
