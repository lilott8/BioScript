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
        self.assertTrue(Identifier.is_chemical_formula('H2O'))
        self.assertTrue(Identifier.is_chemical_formula('C2O'))
        #self.assertTrue(Identifier.is_chemical_formula('Al2(SO4)3'))
        #self.assertTrue(Identifier.is_chemical_formula('(CH3)3CH'))
        #self.assertFalse(Identifier.is_chemical_formula('3('))
        self.assertFalse(Identifier.is_chemical_formula('(H2()'))
        self.assertFalse(Identifier.is_chemical_formula('2HO'))


    def test_smile_validation(self): 
        self.assertTrue(Identifier.is_smiles(r'N#N'))
        self.assertTrue(Identifier.is_smiles(r'CN=C=O'))
        self.assertTrue(Identifier.is_smiles(r'A.A#O2=H+(CCC)$Sa-I\R/E@@@@O'))
        self.assertTrue(Identifier.is_smiles(r'(CNC)'))
        self.assertTrue(Identifier.is_smiles(r'[Cu+2].[O-]S(=O)(=O)[O-]'))
        self.assertTrue(Identifier.is_smiles(r'CC[C@H](O1)CC[C@@]12CCCO2'))
        self.assertTrue(Identifier.is_smiles(r'OC[C@@H](O1)[C@@H](O)[C@H](O)[C@@H](O)[C@@H](O)1'))
        self.assertFalse(Identifier.is_smiles(r''))
        self.assertFalse(Identifier.is_smiles(r'C!!C'))#!! is NOT a valid chemical bond.
        self.assertFalse(Identifier.is_smiles(r'=O=O'))#a chemical bond cannot begin with a bond.
 

    def test_inchi_validation(self):
        self.assertTrue(Identifier.is_inchi_key('InChI=1/C2H6O/c1-2-3/h3H,2H2,1H3'))
        self.assertTrue(Identifier.is_inchi_key('InChI=1/C6H8O6/c7-1-2(8)5-3(9)4(10)6(11)12-5/h2,5,7-10H,1H2/t2-,5+/m0/s1'))
        self.assertFalse(Identifier.is_inchi_key('InChI=1/../c1-2-3/h3H,2H2,1H3'))
        self.assertFalse(Identifier.is_inchi_key(''))
        self.assertFalse(Identifier.is_inchi_key('INCHI'))



