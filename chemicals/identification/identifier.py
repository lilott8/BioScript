import re

class Identifier(object):

    smiles_string    = '^({0}+|\({0}+\)[0-9]*)({1}{0}+|\({1}{0}+\)[0-9]*|{1}\({0}+\)[0-9]*)*$'.format('({0}|\[{0}+\][0-9]*)'.format('(([A-Z][a-z]?|[bncnops])([0-9]*\+*|\+*[0-9]*|[0-9]*\-*|\-*[0-9]*)|@)'), '([\.\-=#$:/\\\\]?)')
    
    cas_number_regex = re.compile('^[0-9]{2,7}-[0-9]{2}-[0-9]$')
    formula_regex    = re.compile('^([A-Z][a-z]?[0-9]*|\(([A-Z][a-z]?[0-9]*)+\)[0-9]*)+$')
    smiles_regex     = re.compile(smiles_string)
    inchi_key_regex  = re.compile('^InChI\=1S?\/[A-Za-z0-9]+(\+[0-9]+)?(\/[cnpbtmshi][A-Za-z0-9\-\+\(\)\,\/]+)*$')


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
        return Identifier.inchi_key_regex.match(string) != None




