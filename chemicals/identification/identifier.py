

class Identifier(object):
     
    cas_number_regex = re.compile('^[0-9].*-.*-.*[0-9]$')

    #direct copy from the Java code.
    formula_regex    = re.compile('[A-Z][a-z]?\\d*|\\((?:[^()]*(?:\\(.*\\)0?[^()]*)+\\)\\d+')
    smiles_regex     = re.compile('OC[C@@H](O1)[C@@H](0)[C@H](0)[C@@H]2[C@@H]1c3c(O)c(OC)c(O)cc3C(=O)O2')
    inchi_key_regex   = re.compile('^([0-9A-Z\\-]+)$')


    def __init__(self):
        pass
  
    @staticmethod
    def is_cas_number(string):
        return DBIdentifier.cas_number_regex.match(string) != None

    @staticmethod
    def is_chemical_formula(string):
        return DBIdentifier.formula_regex.match(string) != None
    
    @staticmethod
    def is_smiles(string):
        return DBIdentifier.smiles_regex.match(string) != None

    @staticmethod
    def is_inchi_key(string):
        return DBIdentifier.inchi_key_regex(string) != None
  



