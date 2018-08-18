from chemicals.identification.identifier import Identifier
from shared.enums.chemtypes import ChemTypes
from shared.enums.config_flags import IdentifyLevel
from shared.variable import Variable


class NaiveIdentifier(Identifier):

    def __init__(self, level: IdentifyLevel):
        super().__init__(level)

    def identify(self, search_for: str, types: set = frozenset(), scope: str = "") -> Variable:
        if not types:
            types = set()
            types.add(ChemTypes.UNKNOWN)
        return Variable(search_for, types, scope)
