import unittest
from chemicals.identification.identifier import Identifier
from chemicals.identification.db_identifier import DBIdentifier
from io.database import Database

class Test_Identifiers(unittest.TestCase):

    def test_cas_number_validation(self): 
        self.assertTrue(Identifier.is_cas_number('12005-69-5'))
        self.assertTrue(Identifier.is_cas_number('13510-31-1'))
        self.assertTrue(Identifier.is_cas_number('10294-33-4'))
        self.assertTrue(Identifier.is_cas_number('541-43-5'))
        self.assertTrue(Identifier.is_cas_number('542-62-1'))
        self.assertTrue(Identifier.is_cas_number('513-77-9'))
        self.assertTrue(Identifier.is_cas_number('75-20-7'))
        self.assertTrue(Identifier.is_cas_number('62-54-4'))
        self.assertTrue(Identifier.is_cas_number('1234567-42-1'))
        self.assertFalse(Identifier.is_cas_number('a1234-49-1'))
        self.assertFalse(Identifier.is_cas_number('12b1-29-1'))
        self.assertFalse(Identifier.is_cas_number('123-1'))
        self.assertFalse(Identifier.is_cas_number('123-39-b'))
        self.assertFalse(Identifier.is_cas_number('2938i-i-i'))
        self.assertFalse(Identifier.is_cas_number(''))
        self.assertFalse(Identifier.is_cas_number('j-we-1'))
        self.assertFalse(Identifier.is_cas_number('fff-13-19'))
        self.assertFalse(Identifier.is_cas_number('8999-f2-11'))
        self.assertFalse(Identifier.is_cas_number('1020-0!-1'))
        self.assertFalse(Identifier.is_cas_number('2938-01o-1'))
        
    def test_database_connection(self):
        db = Database('root', '', 'localhost', 1433, 'chem_trails')
        self.assertTrue(db.is_connected)
        db.close()

    def test_chemical_formula_validation(self):
        #@Incomplete: figure out what a chemical formula looks like...
        pass

    def test_smile_validation(self): 
        self.assertTrue(Identifier.is_smile('N#N')
        self.assertTrue(Identifier.is_smile('CN=C=O')
        self.assertTrue(Identifier.is_smile('[Cu+2].[O-]S(=O)(=O)[O-]')
        self.assertTrue(Identifier.is_smile('OC[C@@H](O1)[C@@H](O)[C@H](O)[C@@H](O)[C@@H](O)1')



if __name__ == '__main__':
    unittest.main()




