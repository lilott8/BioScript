from chemicals.combiner.naive_combiner import NaiveCombiner
from chemicals.combiner.simulate_combiner import SimulateCombiner
from chemicals.identification.db_identifier import DBIdentifier
from chemicals.identification.identifier import Identifier
from chemicals.identification.naive_identifier import NaiveIdentifier
from config.config import Config
from shared.enums.config_flags import ClassifyLevel
from shared.enums.config_flags import IdentifyLevel


def get_identifier(identifier: IdentifyLevel) -> Identifier:
    if identifier == IdentifyLevel.DISABLED or Config.getInstance(None):
        return NaiveIdentifier(identifier)
    else:
        return DBIdentifier(identifier, Config.getInstance(None).db)


def get_combiner(combiner):
    if combiner == ClassifyLevel.SIMULATE:
        return SimulateCombiner()
    else:
        return NaiveCombiner()

