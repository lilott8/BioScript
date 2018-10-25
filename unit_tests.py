import unittest
import time
from chemicals.epa_manager import EpaManager
from chemicals.identification.identifier import Identifier
from shared.enums.chemtypes import ChemTypes
from shared.enums.chemtypes import Consequence
from shared.io.database import Database
from solvers.z3_solver import Z3Solver

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
        '''
        db = Database('root', '', 'localhost', 1433, 'chem_trails')
        self.assertTrue(db.is_connected)
        db.close()
        '''
        pass

    def test_chemical_formula_validation(self):
        self.assertTrue(Identifier.is_chemical_formula(r'NaCl'))
        self.assertTrue(Identifier.is_chemical_formula(r'H2O'))
        self.assertTrue(Identifier.is_chemical_formula(r'C2O'))
        self.assertTrue(Identifier.is_chemical_formula(r'Al2(SO4)3'))
        self.assertTrue(Identifier.is_chemical_formula(r'(CH3)3CH'))
        self.assertTrue(Identifier.is_chemical_formula(r'H(CH3)4(SO4)5(Ba)B'))

        self.assertFalse(Identifier.is_chemical_formula(r'3('))
        self.assertFalse(Identifier.is_chemical_formula(r'(H2()'))
        self.assertFalse(Identifier.is_chemical_formula(r'2HO'))
        self.assertFalse(Identifier.is_chemical_formula(r'A((BO3)'))
        self.assertFalse(Identifier.is_chemical_formula(r'NaCl[]'))

    def test_smile_validation(self):
        self.assertTrue(Identifier.is_smiles(r'[n+]'))
        self.assertTrue(Identifier.is_smiles(r'N#N'))
        self.assertTrue(Identifier.is_smiles(r'CN=C=O'))
        self.assertTrue(Identifier.is_smiles(r'(CNC)'))
        self.assertTrue(Identifier.is_smiles(r'A\A/A.A-A=A#A$A@@@@A'))
        self.assertTrue(Identifier.is_smiles(r'[Cu+2].[O-]S(=O)(=O)[O-]'))
        self.assertTrue(Identifier.is_smiles(r'CC[C@H](O1)CC[C@@]12CCCO2'))
        self.assertTrue(Identifier.is_smiles(r'OC[C@@H](O1)[C@@H](O)[C@H](O)[C@@H](O)[C@@H](O)1'))
        self.assertTrue(Identifier.is_smiles(r'OCCc1c(C)[n+](cs1)Cc2cnc(C)nc2N'))
        self.assertTrue(Identifier.is_smiles(r'CN1CCC[C@H]1c2cccnc2'))
        self.assertTrue(Identifier.is_smiles('C1=CC=CC=C1'))
        self.assertTrue(Identifier.is_smiles('c1ccccc1'))
        self.assertTrue(Identifier.is_smiles('[O-][n+]1ccccc1'))
        self.assertTrue(Identifier.is_smiles('s1cccc1'))
        self.assertTrue(Identifier.is_smiles('[cH-]1cccc1'))
        self.assertTrue(Identifier.is_smiles('[Na+].[Cl-]'))

        self.assertFalse(Identifier.is_smiles(r''))
        self.assertFalse(Identifier.is_smiles(r'(A=#A'))
        self.assertFalse(Identifier.is_smiles(r'C!!C'))
        self.assertFalse(Identifier.is_smiles(r'=O=O'))
        self.assertFalse(Identifier.is_smiles(r'C#=(C)'))

    def test_inchi_validation(self):
        self.assertTrue(Identifier.is_inchi_key(r'InChI=1/C2H6O/c1-2-3/h3H,2H2,1H3'))
        self.assertTrue(Identifier.is_inchi_key(r'InChI=1/C6H8O6/c7-1-2(8)5-3(9)4(10)6(11)12-5/h2,5,7-10H,1H2/t2-,5+/m0/s1'))
        self.assertTrue(Identifier.is_inchi_key(r'InChI=1/C17H13CIN4/c1-11-20-21-16-10-19-17(12-5-3-2-4-6-12)14-9-13(18)7-8-15(14)22(11)16/h2-9H'))

        self.assertFalse(Identifier.is_inchi_key(r'InChI=1/../c1-2-3/h3H,2H2,1H3'))
        self.assertFalse(Identifier.is_inchi_key(r''))
        self.assertFalse(Identifier.is_inchi_key(r'INCHI'))

    def test_epa_manager(self):
        epa = EpaManager('resources/epa.json', 'resources/abstract-interaction.txt')
        self.assertTrue(len(epa.reactive_table) != 0)
        self.assertTrue(len(epa.interactions) != 0)
        self.assertTrue(epa.check_interactions(2, 7) and epa.interactions[2][7] == {1, 2, 3, 4, 68, 5, 7, 39, 8, 10, 44, 13, 45, 14, 16, 51, 59, 61, 29, 31})
        self.assertTrue(epa.check_interactions(76, 99) and epa.interactions[76][99] == {76})
        self.assertTrue(epa.check_interactions(99, 99) and epa.interactions[99][99] == {99})
        self.assertTrue(epa.check_interactions(4, 14) and epa.interactions[4][14] == {4, 14})
        self.assertTrue(not epa.validate(ChemTypes(100), ChemTypes(1)) and epa.reactive_table[100][1] == Consequence.CAUTION)
        self.assertTrue(not epa.validate(ChemTypes(76), ChemTypes(62)) and epa.reactive_table[76][62] == Consequence.CAUTION)
        self.assertTrue(not epa.validate(ChemTypes(31),  ChemTypes(5)) and epa.reactive_table[31][5] == Consequence.INCOMPATIBLE)

    def test_z3solver(self):
        epa = EpaManager('resources/epa.json', 'resources/abstract-interaction.txt')
        #nums = [0, 0, 0, 0, 0, 0, 0, 0, 0]
        self.assertTrue(Z3Solver.solve_file('resources/test9.json', epa.validate, sol=False))
        m = Z3Solver.solve_file('resources/test9.json', epa.validate)
        print(m)
        '''#calculate average runtime
        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test0.json', epa.validate, sol=False))
            x = time.time() - x
            nums[0] += x

        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test1.json', epa.validate, sol=False))
            x = time.time() - x
            nums[1] += x

        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test2.json', epa.validate, sol=False))
            x = time.time() - x
            nums[2] += x

        for i in range(100):
            x = time.time()
            self.assertTrue(Z3Solver.solve_file('resources/test3.json', epa.validate, sol=False))
            x = time.time() - x
            nums[3] += x

        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test4.json', epa.validate, sol=False))
            x = time.time() - x
            nums[4] += x
       
        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test5.json', epa.validate, sol=False))
            x = time.time() - x
            nums[5] += x

        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test6.json', epa.validate, sol=False))
            x = time.time() - x
            nums[6] += x

        for i in range(100):
            x = time.time()
            self.assertFalse(Z3Solver.solve_file('resources/test7.json', epa.validate, sol=False))
            x = time.time() - x
            nums[7] += x

        for i in range(100):
            x = time.time()
            self.assertTrue(Z3Solver.solve_file('resources/test8.json', epa.validate, sol=False))
            x = time.time() - x
            nums[8] += x
 
        for i in range(len(nums)):
            nums[i] /= 100
        print(nums)'''



