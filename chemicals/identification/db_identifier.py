import re
from chemicals.identification.identifier import Identifier
from io.database import Database

class DBIdentifier(Identifier):
    def __init__(self, db):
        Identifier.__init__(self)  
        self.db = db
    
    #according to mysql syntax, '=' means check for equality....
    #check whether name is valid
    def is_name(self, string):
        cursor = self.db.sql_query('SELECT name FROM chemicals WHERE name = {0};'.format(string))
        return len(cursor.fetchone()) != 0 #fetch a single row from cursor

    def search_by_cas_number(self, string):
        cursor = self.db.sql_query('SELECT * FROM cas_numbers WHERE cas_number_string = {0}'.format(string))
        return cursor.fetchall()


    def search_by_inchi_key(self, string):
        cursor = self.db.sql_query('SELECT * FROM chemicals WHERE inchi_key = {0}'.format(string))
        return cursor.fetchall()

    def search_by_smiles(self, string):
        cursor = self.db.sql_query('SELECT * FROM chemicals WHERE isomeric_smiles = {0} OR canonical_smiles = {0}'.format(string))
        return cursor.fetchall()


    def search_by_pub_chem_id(self, string):
        cursor = self.db.sql_query('SELECT * FROM chemicals WHERE pubchem_id = {0}', string)
        return cursor.fetchall()


    def search_by_aliases(self, string):
        cursor = self.db.sql_query('SELECT * FROM chemicals')
        return cursor.fetchall()









