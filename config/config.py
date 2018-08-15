import colorlog

from shared.enums.config_flags import ClassifyLevel
from shared.enums.config_flags import IdentifyLevel
from shared.enums.config_flags import Problem
from shared.enums.config_flags import ReportingLevel
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
        self.input = None
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
        # What is the problem that is being solved.
        self.problem = None

        if Config.__instance is not None:
            raise Exception('This is a singleton.')
        else:
            self.log.warning(args.input)
            self.debug = args.debug
            if args.epa_defs:
                self.epa_defs = args.epa_defs
            self.input = args.input
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

            if args.solver.lower() == "d" or args.solver.lower() == "disable":
                self.typecheck = TypeChecker.DISABLED
            elif args.solver.lower() == "union" or args.solver.lower() == 'u':
                self.typecheck = TypeChecker.UNION
            else:
                self.typecheck = TypeChecker.NAIVE

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
