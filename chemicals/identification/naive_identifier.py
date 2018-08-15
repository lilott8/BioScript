from chemicals.identification.identifier import Identifier
from shared.enums.chemtypes import ChemTypes
from shared.enums.config_flags import IdentifyLevel
from shared.variable import Variable


class NaiveIdentifier(Identifier):

    def __init__(self, level: IdentifyLevel):
        super().__init__(level)

    def identify(self, search_for: str) -> Variable:
        var = Variable(search_for, {ChemTypes.MAT})
        return var
