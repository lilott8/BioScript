import re

class Identifier(object):
     
    cas_number_regex = re.compile('^[0-9].*-.*-.*[0-9]$')
    formula_regex    = re.compile('[A-Z][a-z]?\\d*|\\((?:[^()]*(?:\\(.*\\))?[^()]*)+\\)\\d+')
    smiles_regex     = re.compile('OC[C@@H](O1)[C@@H](0)[C@H](0)[C@@H]2[C@@H]1c3c(O)c(OC)c(O)cc3C(=O)O2')
    inchi_key_regex  = re.compile('^([0-9A-Z\-]+)$')


    def __init__(self):
        pass
  
    @staticmethod
    def is_cas_number(string):
        return Identifier.cas_number_regex.match(string) != None

    @staticmethod
    def is_chemical_formula(string):
        return Identifier.formula_regex.match(string) != None
    
    @staticmethod
    def is_smiles(string):
        return Identifier.smiles_regex.match(string) != None

    @staticmethod
    def is_inchi_key(string):
        return len(string) == 25 \
               and string[14] == '-' \
               and Identifier.inchi_key_regex.match(string) != None
  



