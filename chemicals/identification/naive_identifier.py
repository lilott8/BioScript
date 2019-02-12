from chemicals.identification.identifier import Identifier
from shared.enums.config_flags import IdentifyLevel
from shared.variable import *


class NaiveIdentifier(Identifier):

    def __init__(self, level: IdentifyLevel):
        super().__init__(level)

    def identify(self, search_for: str, types: set = frozenset(), scope: str = "") -> Chemical:
        if not types:
            types = set()
            types.add(ChemTypes.UNKNOWN)
        return Chemical(search_for, types, scope)
