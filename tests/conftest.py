import pytest
from antlr4 import *

from grammar.parsers.python.BSLexer import BSLexer
from grammar.parsers.python.BSParser import BSParser


@pytest.fixture(scope="session")
def get_visitor():
    # This allows us to accept arguments to the fixture.
    def _filename(filename: str):
        file_stream = FileStream(filename)
        lexer = BSLexer(file_stream)
        stream = CommonTokenStream(lexer)
        parser = BSParser(stream)
        return parser.program()

    return _filename
