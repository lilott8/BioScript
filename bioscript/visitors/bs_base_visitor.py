import colorlog

from grammar.parsers.python.BSParserVisitor import BSParserVisitor
from shared.helpers import *


class BSBaseVisitor(BSParserVisitor):

    def __init__(self, symbol_table):
        super().__init__()
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.config = Config.getInstance(None)
        # The identifier to use.
        self.identifier = get_identifier(self.config.identify)
        # The combiner to use.
        self.combiner = get_combiner(self.config.combine)
        self.symbol_table = symbol_table
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

    def check_identifier(self, name):
        if name in self.keywords:
            return "{}{}".format(name, name)
        else:
            return name
