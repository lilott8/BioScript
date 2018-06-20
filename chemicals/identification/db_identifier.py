import re
from chemicals.identification.identifier import Identifier
from io.database import Database

class DBIdentifier(Identifier):
    def __init__(self, db):
        Identifier.__init__(self)  
        self.db = db

    def is_name(self, string):
        self.db.sql_query('SELECT NAME things....')

    def search_by_cas_number(self, string):
        self.db.sql_query('SELECT CAS NUMBER thingy...')

    def search_by_inchi_key(self, string):
        self.db.sql_query('SELECT inchi key thingy...')

    def search_by_smiles(self, string):
        self.db.sql_query('SELECT smiles thingy...')

    def search_by_aliases(self, string):
        self.db.sql_query('SELECT aliases thingy...')

