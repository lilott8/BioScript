from enum import IntEnum


class ChemTypes(IntEnum):
    ACIDS_STRONG_NON_OXIDIZING = 1
    ACIDS_STRONG_OXIDIZING = 2
    ACIDS_CARBOXYLIC = 3
    ALCOHOLS_AND_POLYOLS = 4
    ALDEHYDES = 5
    AMIDES_AND_IMIDES = 6
    AMINES_PHOSPHINES_AND_PYRIDINES = 7
    AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS = 8
    CARBAMATES = 9
    BASES_STRONG = 10
    CYANIDES_INORGANIC = 11
    THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS = 12
    ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS = 13
    ETHERS = 14
    FLUORIDES_INORGANIC = 15
    HYDROCARBONS_AROMATIC = 16
    HALOGENATED_ORGANIC_COMPOUNDS = 17
    ISOCYANATES_AND_ISOTHIOCYANATES = 18
    KETONES = 19
    SULFIDES_ORGANIC = 20
    METALS_ALKALI_VERY_ACTIVE = 21
    METALS_ELEMENTAL_AND_POWDER_ACTIVE = 22
    METALS_LESS_REACTIVE = 23
    DIAZONIUM_SALTS = 25
    NITRILES = 26
    NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC = 27
    HYDROCARBONS_ALIPHATIC_UNSATURATED = 28
    HYDROCARBONS_ALIPHATIC_SATURATED = 29
    PEROXIDES_ORGANIC = 30
    PHENOLS_AND_CRESOLS = 31
    SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC = 32
    SULFIDES_INORGANIC = 33
    EPOXIDES = 34
    METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES = 35
    ANHYDRIDES = 37
    SALTS_ACIDIC = 38
    SALTS_BASIC = 39
    ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES = 40
    ORGANOMETALLICS = 42
    OXIDIZING_AGENTS_STRONG = 44
    REDUCING_AGENTS_STRONG = 45
    NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS = 46
    FLUORINATED_ORGANIC_COMPOUNDS = 47
    FLUORIDE_SALTS_SOLUBLE = 48
    OXIDIZING_AGENTS_WEAK = 49
    REDUCING_AGENTS_WEAK = 50
    NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES = 51
    CHLOROSILANES = 55
    SILOXANES = 58
    HALOGENATING_AGENTS = 59
    ACIDS_WEAK = 60
    BASES_WEAK = 61
    CARBONATE_SALTS = 62
    ALKYNES_WITH_ACETYLENIC_HYDROGEN = 63
    ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN = 64
    CONJUGATED_DIENES = 65
    ARYL_HALIDES = 66
    AMINES_AROMATIC = 68
    NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC = 69
    ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS = 70
    ACRYLATES_AND_ACRYLIC_ACIDS = 71
    PHENOLIC_SALTS = 72
    QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS = 73
    SULFITE_AND_THIOSULFATE_SALTS = 74
    OXIMES = 75
    POLYMERIZABLE_COMPOUNDS = 76
    NOT_CHEMICALLY_REACTIVE = 98
    INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION = 99
    WATER_AND_AQUEOUS_SOLUTIONS = 100
    REAL = 128
    NAT = 129
    MAT = 130
    CONST = 131
    BOOL = 132
    MODULE = 133
    NULL = 134
    UNKNOWN = -1


class ChemTypeResolver(object):
    materials = {ChemTypes.ACIDS_STRONG_NON_OXIDIZING, ChemTypes.ACIDS_STRONG_OXIDIZING, ChemTypes.ACIDS_CARBOXYLIC,
                 ChemTypes.ALCOHOLS_AND_POLYOLS, ChemTypes.ALDEHYDES,
                 ChemTypes.AMIDES_AND_IMIDES, ChemTypes.AMINES_PHOSPHINES_AND_PYRIDINES,
                 ChemTypes.AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS,
                 ChemTypes.CARBAMATES, ChemTypes.BASES_STRONG, ChemTypes.CYANIDES_INORGANIC,
                 ChemTypes.THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS,
                 ChemTypes.ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS,
                 ChemTypes.ETHERS,
                 ChemTypes.FLUORIDES_INORGANIC, ChemTypes.HYDROCARBONS_AROMATIC,
                 ChemTypes.HALOGENATED_ORGANIC_COMPOUNDS, ChemTypes.ISOCYANATES_AND_ISOTHIOCYANATES,
                 ChemTypes.KETONES, ChemTypes.SULFIDES_ORGANIC, ChemTypes.METALS_ALKALI_VERY_ACTIVE,
                 ChemTypes.METALS_ELEMENTAL_AND_POWDER_ACTIVE,
                 ChemTypes.METALS_LESS_REACTIVE, ChemTypes.DIAZONIUM_SALTS, ChemTypes.NITRILES,
                 ChemTypes.NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC,
                 ChemTypes.HYDROCARBONS_ALIPHATIC_SATURATED, ChemTypes.HYDROCARBONS_ALIPHATIC_UNSATURATED,
                 ChemTypes.PEROXIDES_ORGANIC, ChemTypes.PHENOLS_AND_CRESOLS,
                 ChemTypes.SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC,
                 ChemTypes.SULFIDES_INORGANIC, ChemTypes.EPOXIDES,
                 ChemTypes.METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES, ChemTypes.ANHYDRIDES,
                 ChemTypes.SALTS_ACIDIC, ChemTypes.SALTS_BASIC,
                 ChemTypes.ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES,
                 ChemTypes.ORGANOMETALLICS, ChemTypes.OXIDIZING_AGENTS_STRONG, ChemTypes.REDUCING_AGENTS_STRONG,
                 ChemTypes.NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS,
                 ChemTypes.FLUORINATED_ORGANIC_COMPOUNDS, ChemTypes.FLUORIDE_SALTS_SOLUBLE,
                 ChemTypes.OXIDIZING_AGENTS_WEAK, ChemTypes.REDUCING_AGENTS_WEAK,
                 ChemTypes.NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES,
                 ChemTypes.CHLOROSILANES, ChemTypes.SILOXANES, ChemTypes.HALOGENATING_AGENTS, ChemTypes.ACIDS_WEAK,
                 ChemTypes.BASES_WEAK, ChemTypes.CARBONATE_SALTS,
                 ChemTypes.ALKYNES_WITH_ACETYLENIC_HYDROGEN, ChemTypes.ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN,
                 ChemTypes.CONJUGATED_DIENES, ChemTypes.ARYL_HALIDES,
                 ChemTypes.AMINES_AROMATIC, ChemTypes.NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC,
                 ChemTypes.ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS, ChemTypes.PHENOLIC_SALTS,
                 ChemTypes.QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS,
                 ChemTypes.SULFITE_AND_THIOSULFATE_SALTS, ChemTypes.OXIMES, ChemTypes.POLYMERIZABLE_COMPOUNDS,
                 ChemTypes.NOT_CHEMICALLY_REACTIVE,
                 ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION, ChemTypes.WATER_AND_AQUEOUS_SOLUTIONS,
                 ChemTypes.MAT}

    numbers = (ChemTypes.REAL, ChemTypes.MAT, ChemTypes.CONST, ChemTypes.BOOL)

    available_types = {ChemTypes.ACIDS_STRONG_NON_OXIDIZING, ChemTypes.ACIDS_STRONG_OXIDIZING,
                       ChemTypes.ACIDS_CARBOXYLIC,
                       ChemTypes.ALCOHOLS_AND_POLYOLS, ChemTypes.ALDEHYDES,
                       ChemTypes.AMIDES_AND_IMIDES, ChemTypes.AMINES_PHOSPHINES_AND_PYRIDINES,
                       ChemTypes.AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS,
                       ChemTypes.CARBAMATES, ChemTypes.BASES_STRONG, ChemTypes.CYANIDES_INORGANIC,
                       ChemTypes.THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS,
                       ChemTypes.ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS,
                       ChemTypes.ETHERS,
                       ChemTypes.FLUORIDES_INORGANIC, ChemTypes.HYDROCARBONS_AROMATIC,
                       ChemTypes.HALOGENATED_ORGANIC_COMPOUNDS, ChemTypes.ISOCYANATES_AND_ISOTHIOCYANATES,
                       ChemTypes.KETONES, ChemTypes.SULFIDES_ORGANIC, ChemTypes.METALS_ALKALI_VERY_ACTIVE,
                       ChemTypes.METALS_ELEMENTAL_AND_POWDER_ACTIVE,
                       ChemTypes.METALS_LESS_REACTIVE, ChemTypes.DIAZONIUM_SALTS, ChemTypes.NITRILES,
                       ChemTypes.NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC,
                       ChemTypes.HYDROCARBONS_ALIPHATIC_SATURATED, ChemTypes.HYDROCARBONS_ALIPHATIC_UNSATURATED,
                       ChemTypes.PEROXIDES_ORGANIC, ChemTypes.PHENOLS_AND_CRESOLS,
                       ChemTypes.SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC,
                       ChemTypes.SULFIDES_INORGANIC, ChemTypes.EPOXIDES,
                       ChemTypes.METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES, ChemTypes.ANHYDRIDES,
                       ChemTypes.SALTS_ACIDIC, ChemTypes.SALTS_BASIC,
                       ChemTypes.ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES,
                       ChemTypes.ORGANOMETALLICS, ChemTypes.OXIDIZING_AGENTS_STRONG, ChemTypes.REDUCING_AGENTS_STRONG,
                       ChemTypes.NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS,
                       ChemTypes.FLUORINATED_ORGANIC_COMPOUNDS, ChemTypes.FLUORIDE_SALTS_SOLUBLE,
                       ChemTypes.OXIDIZING_AGENTS_WEAK, ChemTypes.REDUCING_AGENTS_WEAK,
                       ChemTypes.NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES,
                       ChemTypes.CHLOROSILANES, ChemTypes.SILOXANES, ChemTypes.HALOGENATING_AGENTS,
                       ChemTypes.ACIDS_WEAK,
                       ChemTypes.BASES_WEAK, ChemTypes.CARBONATE_SALTS,
                       ChemTypes.ALKYNES_WITH_ACETYLENIC_HYDROGEN, ChemTypes.ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN,
                       ChemTypes.CONJUGATED_DIENES, ChemTypes.ARYL_HALIDES,
                       ChemTypes.AMINES_AROMATIC, ChemTypes.NITRATE_AND_NITRITE_COMPOUNDS_INORGANIC,
                       ChemTypes.ACETALS_KETALS_HEMIACETALS_AND_HEMIKETALS, ChemTypes.PHENOLIC_SALTS,
                       ChemTypes.QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS,
                       ChemTypes.SULFITE_AND_THIOSULFATE_SALTS, ChemTypes.OXIMES, ChemTypes.POLYMERIZABLE_COMPOUNDS,
                       ChemTypes.NOT_CHEMICALLY_REACTIVE,
                       ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION, ChemTypes.WATER_AND_AQUEOUS_SOLUTIONS,
                       ChemTypes.REAL, ChemTypes.NAT}

    naive_types = {ChemTypes.REAL, ChemTypes.MAT, ChemTypes.NAT}

    @staticmethod
    def is_mat(value):
        return value in ChemTypeResolver.materials

    @staticmethod
    def is_number(value):
        return value in ChemTypeResolver.numbers

    @staticmethod
    def string_to_type(chemtype: str) -> ChemTypes:
        chemtype = chemtype.upper().replace(",", "").replace(" ", "_")
        if chemtype == 'ACIDS_STRONG_NON_OXIDIZING':
            return ChemTypes.ACIDS_STRONG_NON_OXIDIZING
        elif chemtype == 'ACIDS_STRONG_OXIDIZING':
            return ChemTypes.ACIDS_STRONG_OXIDIZING
        elif chemtype == 'ACIDS_CARBOXYLIC':
            return ChemTypes.ACIDS_CARBOXYLIC
        elif chemtype == 'ALCOHOLS_AND_POLYOLS':
            return ChemTypes.ALCOHOLS_AND_POLYOLS
        elif chemtype == 'ALDEHYDES':
            return ChemTypes.ALDEHYDES
        elif chemtype == 'AMIDES_AND_IMIDES':
            return ChemTypes.AMIDES_AND_IMIDES
        elif chemtype == 'AMINES_PHOSPHINES_AND_PYRIDINES':
            return ChemTypes.AMINES_PHOSPHINES_AND_PYRIDINES
        elif chemtype == 'AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS':
            return ChemTypes.AZO_DIAZO_AZIDO_HYDRAZINE_AND_AZIDE_COMPOUNDS
        elif chemtype == 'CARBAMATES':
            return ChemTypes.CARBAMATES
        elif chemtype == 'BASES_STRONG':
            return ChemTypes.BASES_STRONG
        elif chemtype == 'CYANIDES_INORGANIC':
            return ChemTypes.CYANIDES_INORGANIC
        elif chemtype == 'THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS':
            return ChemTypes.THIOCARBAMATE_ESTERS_AND_SALTS_DITHIOCARBAMATE_ESTERS_AND_SALTS
        elif chemtype == 'ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS':
            return ChemTypes.ESTERS_SULFATE_ESTERS_PHOSPHATE_ESTERS_THIOPHOSPHATE_ESTERS_AND_BORATE_ESTERS
        elif chemtype == 'ETHERS':
            return ChemTypes.ETHERS
        elif chemtype == 'FLUORIDES_INORGANIC':
            return ChemTypes.FLUORIDES_INORGANIC
        elif chemtype == 'HYDROCARBONS_AROMATIC':
            return ChemTypes.HYDROCARBONS_AROMATIC
        elif chemtype == 'HALOGENATED_ORGANIC_COMPOUNDS':
            return ChemTypes.HALOGENATED_ORGANIC_COMPOUNDS
        elif chemtype == 'ISOCYANATES_AND_ISOTHIOCYANATES':
            return ChemTypes.ISOCYANATES_AND_ISOTHIOCYANATES
        elif chemtype == 'KETONES':
            return ChemTypes.KETONES
        elif chemtype == 'SULFIDES_ORGANIC':
            return ChemTypes.SULFIDES_ORGANIC
        elif chemtype == 'METALS_ALKALI_VERY_ACTIVE':
            return ChemTypes.METALS_ALKALI_VERY_ACTIVE
        elif chemtype == 'METALS_ELEMENTAL_AND_POWDER_ACTIVE':
            return ChemTypes.METALS_ELEMENTAL_AND_POWDER_ACTIVE
        elif chemtype == 'METALS_LESS_REACTIVE':
            return ChemTypes.METALS_LESS_REACTIVE
        elif chemtype == 'DIAZONIUM_SALTS':
            return ChemTypes.DIAZONIUM_SALTS
        elif chemtype == 'NITRILES':
            return ChemTypes.NITRILES
        elif chemtype == 'NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC':
            return ChemTypes.NITRO_NITROSO_NITRATE_AND_NITRITE_COMPOUNDS_ORGANIC
        elif chemtype == 'HYDROCARBONS_ALIPHATIC_UNSATURATED':
            return ChemTypes.HYDROCARBONS_ALIPHATIC_UNSATURATED
        elif chemtype == 'HYDROCARBONS_ALIPHATIC_SATURATED':
            return ChemTypes.HYDROCARBONS_ALIPHATIC_SATURATED
        elif chemtype == 'PEROXIDES_ORGANIC':
            return ChemTypes.PEROXIDES_ORGANIC
        elif chemtype == 'PHENOLS_AND_CRESOLS':
            return ChemTypes.PHENOLS_AND_CRESOLS
        elif chemtype == 'SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC':
            return ChemTypes.SULFONATES_PHOSPHONATES_AND_THIOPHOSPHONATES_ORGANIC
        elif chemtype == 'SULFIDES_INORGANIC':
            return ChemTypes.SULFIDES_INORGANIC
        elif chemtype == 'EPOXIDES':
            return ChemTypes.EPOXIDES
        elif chemtype == 'METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES':
            return ChemTypes.METAL_HYDRIDES_METAL_ALKYLS_METAL_ARYLS_AND_SILANES
        elif chemtype == 'ANHYDRIDES':
            return ChemTypes.ANHYDRIDES
        elif chemtype == 'SALTS_ACIDIC':
            return ChemTypes.SALTS_ACIDIC
        elif chemtype == 'SALTS_BASIC':
            return ChemTypes.SALTS_BASIC
        elif chemtype == 'ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES':
            return ChemTypes.ACYL_HALIDES_SULFONYL_HALIDES_AND_CHLOROFORMATES
        elif chemtype == 'ORGANOMETALLICS':
            return ChemTypes.ORGANOMETALLICS
        elif chemtype == 'OXIDIZING_AGENTS_STRONG':
            return ChemTypes.OXIDIZING_AGENTS_STRONG
        elif chemtype == 'REDUCING_AGENTS_STRONG':
            return ChemTypes.REDUCING_AGENTS_STRONG
        elif chemtype == 'NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS':
            return ChemTypes.NON_REDOX_ACTIVE_INORGANIC_COMPOUNDS
        elif chemtype == 'FLUORINATED_ORGANIC_COMPOUNDS':
            return ChemTypes.FLUORINATED_ORGANIC_COMPOUNDS
        elif chemtype == 'FLUORIDE_SALTS_SOLUBLE':
            return ChemTypes.FLUORIDE_SALTS_SOLUBLE
        elif chemtype == 'OXIDIZING_AGENTS_WEAK':
            return ChemTypes.OXIDIZING_AGENTS_WEAK
        elif chemtype == 'REDUCING_AGENTS_WEAK':
            return ChemTypes.REDUCING_AGENTS_WEAK
        elif chemtype == 'NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES':
            return ChemTypes.NITRIDES_PHOSPHIDES_CARBIDES_AND_SILICIDES
        elif chemtype == 'CHLOROSILANES':
            return ChemTypes.CHLOROSILANES
        elif chemtype == 'SILOXANES':
            return ChemTypes.SILOXANES
        elif chemtype == 'HALOGENATING_AGENTS':
            return ChemTypes.HALOGENATING_AGENTS
        elif chemtype == 'ACIDS_WEAK':
            return ChemTypes.ACIDS_WEAK
        elif chemtype == 'BASES_WEAK':
            return ChemTypes.BASES_WEAK
        elif chemtype == 'CARBONATE_SALTS':
            return ChemTypes.CARBONATE_SALTS
        elif chemtype == 'ALKYNES_WITH_ACETYLENIC_HYDROGEN':
            return ChemTypes.ALKYNES_WITH_ACETYLENIC_HYDROGEN
        elif chemtype == 'ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN':
            return ChemTypes.ALKYNES_WITH_NO_ACETYLENIC_HYDROGEN
        elif chemtype == 'PHENOLIC_SALTS':
            return ChemTypes.PHENOLIC_SALTS
        elif chemtype == 'QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS':
            return ChemTypes.QUATERNARY_AMMONIUM_AND_PHOSPHONIUM_SALTS
        elif chemtype == 'SULFITE_AND_THIOSULFATE_SALTS':
            return ChemTypes.SULFITE_AND_THIOSULFATE_SALTS
        elif chemtype == 'OXIMES':
            return ChemTypes.OXIMES
        elif chemtype == 'POLYMERIZABLE_COMPOUNDS':
            return ChemTypes.POLYMERIZABLE_COMPOUNDS
        elif chemtype == 'NOT_CHEMICALLY_REACTIVE':
            return ChemTypes.NOT_CHEMICALLY_REACTIVE
        elif chemtype == 'INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION':
            return ChemTypes.INSUFFICIENT_INFORMATION_FOR_CLASSIFICATION
        elif chemtype == 'WATER_AND_AQUEOUS_SOLUTIONS':
            return ChemTypes.WATER_AND_AQUEOUS_SOLUTIONS
        elif chemtype == 'REAL':
            return ChemTypes.REAL
        elif chemtype == 'NAT':
            return ChemTypes.NAT
        elif chemtype == 'MAT':
            return ChemTypes.MAT
        elif chemtype == 'CONST':
            return ChemTypes.CONST
        elif chemtype == 'BOOL':
            return ChemTypes.BOOL
        elif chemtype == 'MODULE':
            return ChemTypes.MODULE
        elif chemtype == 'NULL':
            return ChemTypes.NULL
        elif chemtype == 'UNKNOWN':
            return ChemTypes.UNKNOWN
        else:
            return ChemTypes.UNKNOWN

class Consequence(IntEnum):
    HEAT_GENERATION = 0
    FIRE = 1
    INNOCUOUS_AND_NON_FLAMMABLE_GAS_GENERATION = 2
    TOXIC_GAS_FORMATION = 3
    FLAMMABLE_GAS_FORMATION = 4
    EXPLOSION = 5
    VIOLENT_POLYMERIZATION = 6
    SOLUBILIZATION_OF_TOXIC_SUBSTANCE = 7
    UNKNOWN = 8
    WATER_REACTIVE_SUBSTANCE = 9
    INCOMPATIBLE = 10
    CAUTION = 11
    SELF_REACTIVE = 12

    def get_type_from_id(self, x):
        return x
