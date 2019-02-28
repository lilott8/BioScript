from chemicals.identification.identifier import Identifier
from shared.enums.chemtypes import ChemTypes
from shared.variable import Chemical


class NaiveIdentifier(Identifier):

    def __init__(self):
        super().__init__()

    def identify(self, search_for: str, types: set = frozenset(), scope: str = "") -> Chemical:
        if not types:
            types = set()
            types.add(ChemTypes.UNKNOWN)
        return Chemical(search_for, types, scope)
