import os
import sys

import colorlog

import chemicals.chemtypes as ct
import chemicals.combiner as combiner
import chemicals.identifier as identifier
import compiler.targets.base_target as target


class Config(object):

    def __init__(self, args=None):
        self.log = colorlog.getLogger(self.__class__.__name__)
        """
        General Stuff
        """
        self.debug = False
        self.epa_defs = '/resources/epa_defs.json'
        self.abstract_interaction = '/resources/abstract-interaction.txt'
        self.input = None
        self.input_file = None

        """
        Chemical Stuff
        """
        # For classification, how big of filters to use.
        self.combine = combiner.CombineMethod.NAIVE
        self.smarts_length = 5
        self.filters = False
        # How to identify a chemical.
        self.identify = 4
        # What level to report things.
        self.error_level = ct.ReportingLevel.ERROR
        self.typecheck = combiner.TypeCheckLevel.NAIVE

        """
        Compiler Stuff
        """
        # What is the target?
        self.target = target.Target.INKWELL
        self.supports_functions = False
        self.supports_recursion = False
        self.supports_nesting = False

        """
        Necessary for identify
        """
        self.db_enabled = False
        # Database stuff.
        self.db = {'name': None, 'pass': None, 'addr': None, 'user': None, 'driver': None}

        """
        Build the config object now.
        """
        # self.log.warning(args)
        self.debug = args.debug
        self.path = os.path.dirname(sys.modules['__main__'].__file__)
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
        self.identify = identifier.IdentifyLevel(args.identify)
        if args.simulate:
            self.combine = combiner.CombineMethod.SIMULATE
        else:
            self.combine = combiner.CombineMethod.NAIVE

        if args.typechecklevel.lower() == "none":
            self.error_level = ct.ReportingLevel.NONE
        elif args.typechecklevel.lower() == "warn":
            self.error_level = ct.ReportingLevel.WARNING
        else:
            self.error_level = ct.ReportingLevel.ERROR

        if args.typecheck.lower() == "d" or args.typecheck.lower() == "disable":
            self.typecheck = combiner.TypeCheckLevel.DISABLED
        elif args.typecheck.lower() == "union" or args.typecheck.lower() == 'u':
            self.typecheck = combiner.TypeCheckLevel.UNION
        else:
            self.typecheck = combiner.TypeCheckLevel.NAIVE

        if args.target is not None:
            """
            The support_* flags are defaulted above,
            so we just toggle the necessary flags when
            necessary.
            """
            if args.target.lower() == "m" or args.target.lower() == "mfsim":
                self.target = target.Target.MFSIM
                self.supports_functions = True
                self.supports_nesting = True
            elif args.target.lower() == 'i' or args.target.lower() == 'inkwell':
                self.target = target.Target.INKWELL
                self.supports_functions = True
            elif args.target.lower() == "p" or args.target.lower() == "puddle":
                self.target = target.Target.PUDDLE
                self.supports_functions = True
                self.supports_recursion = True
                self.supports_nesting = True

        if self.db['name'] and self.db['user'] and self.db['pass']:
            self.db_enabled = True
            if not self.db['addr']:
                self.db['addr'] = 'localhost'
            if not self.db['driver']:
                self.db['driver'] = 'mysql'

        # if args.problem == 'i' or args.problem == 'inkwell':
        #     self.problem = Problem.INKWELL
        # elif args.problem == 's' or args.problem == 'store':
        #     self.problem = Problem.STORAGE
        # elif args.problem == 'd' or args.problem == 'disposal':
        #     self.problem = Problem.DISPOSAL
        # elif args.problem == 'm' or args.problem == 'mix':
        #     self.problem = Problem.MIX
