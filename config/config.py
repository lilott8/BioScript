import colorlog

from shared.enums.config_flags import ClassifyLevel
from shared.enums.config_flags import IdentifyLevel
from shared.enums.config_flags import Problem
from shared.enums.config_flags import ReportingLevel
from shared.enums.config_flags import Target
from shared.enums.config_flags import TypeChecker


class Config(object):
    """
    A singleton config object that allows us to maintain state regardless of
    where it is accessed.  We keep our global configuration state here.
    This ensures we can access at all points of our system.
    """
    __instance = None

    @staticmethod
    def getInstance(args=None):
        if Config.__instance is None:
            Config(args)
        return Config.__instance

    def __init__(self, args=None):
        self.log = colorlog.getLogger(self.__class__.__name__)
        self.db_enabled = False
        self.debug = False
        self.epa_defs = './resources/epa_defs.json'
        self.abstract_interaction = './resources/abstract-interaction.txt'
        self.input = None
        self.input_file = None
        self.typecheck = TypeChecker.NAIVE
        # Database stuff.
        self.db = {'name': None, 'pass': None, 'addr': None, 'user': None, 'driver': None}
        # For classification, how big of filters to use.
        self.combine = ClassifyLevel.NAIVE
        self.smarts_length = 5
        self.filters = False
        # How to identify a chemical.
        self.identify = 4
        # What level to report things.
        self.error_level = ReportingLevel.ERROR
        # What is the target?
        self.target = Target.LLVM_IR
        # Use LLVM for optimizations
        self.llvm = False
        # What is the problem that is being solved.
        self.problem = None
        self.path = "./"
        self.supports_functions = True
        self.supports_recursion = False

        if Config.__instance is not None:
            raise Exception('This is a singleton.')
        else:
            # self.log.warning(args)
            self.debug = args.debug
            self.llvm = args.llvm
            self.path = args.path
            if args.epa_defs:
                self.epa_defs = args.epa_defs
            if args.abs_int:
                self.abstract_interaction = args.abs_int
            self.input = args.input
            # Converts: /path/to/bioscript.bs => bioscript
            self.input_file = args.input.split("/")[-1].split(".")[0]
            # self.log.info(self.input_file)
            self.db['name'] = args.dbname
            self.db['user'] = args.dbuser
            self.db['pass'] = args.dbpass
            self.db['addr'] = args.dbaddr
            self.db['driver'] = args.dbdriver
            self.smarts_length = args.smarts
            self.filters = not args.no_filters
            self.identify = IdentifyLevel(args.identify)
            if args.simulate:
                self.combine = ClassifyLevel.SIMULATE
            else:
                self.combine = ClassifyLevel.NAIVE

            if args.level.lower() == "none":
                self.error_level = ReportingLevel.NONE
            elif args.level.lower() == "warn":
                self.error_level = ReportingLevel.WARNING
            else:
                self.error_level = ReportingLevel.ERROR

            if args.typecheck.lower() == "d" or args.typecheck.lower() == "disable":
                self.typecheck = TypeChecker.DISABLED
            elif args.typecheck.lower() == "union" or args.typecheck.lower() == 'u':
                self.typecheck = TypeChecker.UNION
            else:
                self.typecheck = TypeChecker.NAIVE

            if args.target is not None:
                if args.target.lower() == "m" or args.target.lower() == "mfsim":
                    self.target = Target.MFSIM
                    self.supports_functions = True
                    self.supports_recursion = False
                elif args.target.lower() == "i" or args.target.lower() == "inkwell":
                    self.target = Target.INKWELL
                    self.supports_functions = False
                    self.supports_recursion = False
                elif args.target.lower() == "p" or args.target.lower() == "puddle":
                    self.target = Target.PUDDLE
                    self.supports_functions = True
                    self.supports_recursion = True

            if self.db['name'] and self.db['user'] and self.db['pass']:
                self.db_enabled = True
                if not self.db['addr']:
                    self.db['addr'] = 'localhost'
                if not self.db['driver']:
                    self.db['driver'] = 'mysql'

            if args.store:
                self.problem = Problem.STORAGE
            elif args.disposal:
                self.problem = Problem.DISPOSAL
            elif args.mix:
                self.problem = Problem.MIX
            else:
                self.problem = Problem.BIOSCRIPT
            Config.__instance = self
