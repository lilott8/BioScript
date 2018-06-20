import re
from chemicals.identification.identifier import Identifier


class DBIdentifier(Identifier):
    def __init__(self, db):
        Identifier.__init__(self)  
        self.db = db




