from enum import IntEnum

from chemicals.combiner.naive_combiner import NaiveCombiner
from chemicals.combiner.simulate_combiner import SimulateCombiner
from chemicals.identification.db_identifier import DBIdentifier
from chemicals.identification.identifier import Identifier
from chemicals.identification.naive_identifier import NaiveIdentifier


class IdentifyLevel(IntEnum):
    DISABLED = 0
    PUBCHEM_ID = 1
    INCHL_KEY = 2
    CAS_NUMBER = 4
    SMILES = 8
    FORMULA = 16
    NAME = 32

    def get_identifier(self, db: dict = None) -> Identifier:
        if self.value == IdentifyLevel.DISABLED:
            return NaiveIdentifier()
        elif db is not None:
            return DBIdentifier(db)
        else:
            return NaiveIdentifier()


class ClassifyLevel(IntEnum):
    NAIVE = 1
    SIMULATE = 2

    def get_combiner(self, config: 'Config'):
        if self.value == ClassifyLevel.SIMULATE:
            return SimulateCombiner(config)
        else:
            return NaiveCombiner(config)
