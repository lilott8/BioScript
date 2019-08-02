import re
from abc import abstractmethod, ABCMeta
from enum import IntEnum
from typing import Set

from chemicals.chemtypes import ChemTypes, ChemTypeResolver
from shared.bs_exceptions import IdentificationException


class Identifier(metaclass=ABCMeta):
    smiles_string = r'^({0}+|\({0}+\)[0-9]*)({1}{0}+|\({1}{0}+\)[0-9]*|{1}\({0}+\)[0-9]*)*$'.format(
        r'({0}|\[{0}+\][0-9]*)'.format(r'(([A-Z][a-z]?|[bncnops])([0-9]*\+*|\+*[0-9]*|[0-9]*\-*|\-*[0-9]*)|@)'),
        r'([\.\-=#$:/\\\\]?)')

    cas_number_regex = re.compile(r'^[0-9]{2,7}-[0-9]{2}-[0-9]$')
    formula_regex = re.compile(r'^([A-Z][a-z]?[0-9]*|\(([A-Z][a-z]?[0-9]*)+\)[0-9]*)+$')
    smiles_regex = re.compile(smiles_string)
    inchi_key_regex = re.compile(r'^InChI\=1S?\/[A-Za-z0-9]+(\+[0-9]+)?(\/[cnpbtmshi][A-Za-z0-9\-\+\(\)\,\/]+)*$')

    def __init__(self):
        pass

    @abstractmethod
    def identify(self, search_for: str, types: Set = Set) -> Set:
        raise NotImplementedError

    @staticmethod
    def is_cas_number(string) -> bool:
        return Identifier.cas_number_regex.match(string) is not None

    @staticmethod
    def is_chemical_formula(string) -> bool:
        return Identifier.formula_regex.match(string) is not None

    @staticmethod
    def is_smiles(string) -> bool:
        return Identifier.smiles_regex.match(string) is not None

    @staticmethod
    def is_inchi_key(string) -> bool:
        return Identifier.inchi_key_regex.match(string) is not None


class IdentifyLevel(IntEnum):
    DISABLED = 0
    PUBCHEM_ID = 1
    INCHL_KEY = 2
    CAS_NUMBER = 4
    SMILES = 8
    FORMULA = 16
    NAME = 32

    def get_identifier(self, db: dict = None) -> Identifier:
        if self.value == IdentifyLevel.DISABLED:
            return NaiveIdentifier()
        elif db is not None:
            return DBIdentifier(db)
        else:
            return NaiveIdentifier()


class DBIdentifier(Identifier):

    def __init__(self, db):
        super().__init__()
        self.db = db

    def identify(self, search_for: str, types: Set = Set) -> Set:
        self.log.fatal("DB Identifier isn't functioning correctly.")
        return types

    # fix(daniel): figure out if there is a way to prevent exceptions from firing...
    def is_name(self, string):
        try:
            cursor = self.db.sql_query('SELECT name FROM chemicals WHERE name = {0};'.format(string))
            cursor.close()
            return True
        except IdentificationException:
            return False

    def is_pub_chem_id(self, string):
        try:
            cursor = self.db.sql_query('SELECT * FROM chemicals WHERE pubchem_id = {0}'.format(string))
            cursor.close()
            return True
        except IdentificationException:
            return False

    def search_by_cas_number(self, string):
        cursor = self.db.sql_query('SELECT * FROM cas_numbers WHERE cas_number_string = {0}'.format(string))
        return cursor.fetchall()

    def search_by_inchi_key(self, string):
        cursor = self.db.sql_query('SELECT * FROM chemicals WHERE inchi_key = {0}'.format(string))
        return cursor.fetchall()

    def search_by_smiles(self, string):
        cursor = self.db.sql_query(
            'SELECT * FROM chemicals WHERE isomeric_smiles = {0} OR canonical_smiles = {0}'.format(string))
        return cursor.fetchall()

    def search_by_pub_chem_id(self, string):
        cursor = self.db.sql_query('SELECT * FROM chemicals WHERE pubchem_id = {0}'.format(string))
        return cursor.fetchall()

    def search_by_aliases(self, string):
        raise NotImplementedError()


class NaiveIdentifier(Identifier):

    def __init__(self):
        super().__init__()

    def identify(self, search_for: str, types: Set = set()) -> Set:
        if not ChemTypeResolver.is_mat_in_set(types):
            types.add(ChemTypes.MAT)
        return types
