import re

class Identifier(object):

    smiles_string    = "^({0}+|\[{0}+\]|\({0}+\))({1}({0}+|\[{0}+\]|\({0}+\)))*$".format("([A-Z][a-z]?([0-9]*\+*|\+*[0-9]*|\-*[0-9]*|[0-9]*\-*)|@)", "([\.\-=#$:/\\\\]?)")
    
    cas_number_regex = re.compile('^[0-9]{2,7}-[0-9]{2}-[0-9]$')
    formula_regex    = re.compile('^(\(?[A-Z][a-z]?\\d*\)?)+$')
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



 
def test(function, string):
    if function(string) == False:
        print("***TEST FAIL. String: {0}".format(string))
    else:
        print("Sucess: {0}".format(string))


def function():
    print(Identifier.smiles_string)
    test(Identifier.is_smiles,    r"C")
    test(Identifier.is_smiles,  r"(C)")
    test(Identifier.is_smiles, r"[Ca]")
    test(Identifier.is_smiles,  r"CaS")
    test(Identifier.is_smiles,  r"C#N")
    test(Identifier.is_smiles,  r"C.C")
    test(Identifier.is_smiles,  r"C:C")
    test(Identifier.is_smiles,  r"C-C")
    test(Identifier.is_smiles,  r"C=C")
    test(Identifier.is_smiles,  r"C$C")
    test(Identifier.is_smiles,  r"C/C")
    test(Identifier.is_smiles,  r"C\C")
    test(Identifier.is_smiles,  r"CN-C(N)-(C)N")
    test(Identifier.is_smiles,  r"C(H)-C")
    test(Identifier.is_smiles,  r"CC1CCC/CC=C1/C=C/C")
    test(Identifier.is_smiles,  r"OH+")
    test(Identifier.is_smiles,  r"OH-")
    test(Identifier.is_smiles,  r"OH++4")
    test(Identifier.is_smiles,  r"O(C)HH=O-(W)(H)")
    test(Identifier.is_smiles,  r"OH-")
    test(Identifier.is_smiles,  r"O+++4")
    test(Identifier.is_smiles,  r"CC1CCC/C(C)=C1/C=C/C(C)=C/C(C)=C/C=C/C(C)=C/C=C/C=C(C)")
    test(Identifier.is_smiles,  r"O--4--")
    test(Identifier.is_smiles,  r"[Ti4+]")  



if __name__ == '__main__':
    function()






