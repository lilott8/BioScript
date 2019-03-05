from chemicals.chemtypes import ChemTypes


class ReactiveGroup(object):

    def __init__(self, rgid: int, name: str, filters: dict, reactions: dict):
        self.rgid = rgid
        self.name = name
        self.filters = filters
        self.reactions = reactions
        self.type = ChemTypes(rgid)
