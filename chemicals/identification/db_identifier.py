import sys
if __name__ == '__main__': sys.path[0] = (sys.path[0][:-25])
from chemicals.identification.identifier import Identifier
from io.database import Database

class DBIdentifier(Identifier):

    def __init__(self, db):
        Identifier.__init__(self)  
        self.db = db
    
    #fix(daniel): figure out if there is a way to prevent exceptions from firing... 
    def is_name(self, string):
        try:
            cursor = self.db.sql_query('SELECT name FROM chemicals WHERE name = {0};'.format(string))
            cursor.close()
            return True
        except:
            return False


    def is_pub_chem_id(self, string):
        try:
            cursor = self.db.sql_query('SELECT * FROM chemicals WHERE pubchem_id = {0}'.format(string))
            cursor.close()
            return True
        except:
            return False

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
        cursor = self.db.sql_query('SELECT * FROM chemicals WHERE pubchem_id = {0}'.format(string))
        return cursor.fetchall()


    def search_by_aliases(self, string):
        raise NotImplementedError()



