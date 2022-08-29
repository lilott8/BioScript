import os
import sys

import colorlog

import chemicals.chemtypes as ct
import chemicals.combiner as combiner
import chemicals.identifier as identifier
import compiler.semantics.type_visitor as tv
import compiler.targets.target_selector as targets
from compiler.data_structures.properties import BSVolume
from shared.components import FlowType


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
        self.output = './'
        self.write_out = False
        self.print_stats = False
        self.units = BSVolume.get_from_string(args.units)

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
        self.typecheck = True
        self.types_used = tv.TypesUsed.SIMPLE

        """
        Compiler Stuff
        """
        # What is the target?
        self.target = targets.TargetSelector.DISABLED
        self.supports_functions = False
        self.supports_recursion = False
        self.supports_nesting = False
        self.write_cfg = args.write_cfg
        self.inline = False
        self.loopunroll = False
        self.track_volume = False
        """
        Necessary for identify
        """
        self.db_enabled = False
        # Database stuff.
        self.db = {'name': None, 'pass': None, 'addr': None, 'user': None, 'driver': None}

        """
        Inkwell Stuff
        """
        self.library = './resources/flow/components.json'
        self.flow_type = FlowType.PASSIVE
        self.use_local_db = True
        self.schema = './resources/flow/parchmint_schema.json'
        self.validate_schema = False

        """
        Build the config object now.
        """
        # self.log.warning(args)
        self.debug = args.debug
        self.output = args.output
        # makes directory if it doesn't exist
        if args.output:
            os.makedirs(self.output, exist_ok=True)
        self.print_stats = args.stats
        self.path = os.path.dirname(sys.modules['__main__'].__file__)
        if args.output:
            self.write_out = True
            self.output = os.path.abspath(args.output)

        if args.epa_defs:
            self.epa_defs = args.epa_defs
        if args.abs_int:
            self.abstract_interaction = args.abs_int
        self.input = args.input
        # Converts: /path/to/bioscript.bs => bioscript
        self.input_file = args.input.split("/")[-1].split(".")[0]
        self.inline = args.inline
        # self.log.info(self.input_file)
        self.db['name'] = args.dbname
        self.db['user'] = args.dbuser
        self.db['pass'] = args.dbpass
        self.db['addr'] = args.dbaddr
        self.db['driver'] = args.dbdriver
        self.smarts_length = args.smarts
        self.filters = not args.no_filters
        self.identify = identifier.IdentifyLevel(args.identify)

        if args.loopunroll:
            self.loopunroll = True

        if args.track_volume:
            self.track_volume = True

        if args.typechecklevel.lower() == "none":
            self.error_level = ct.ReportingLevel.NONE
        elif args.typechecklevel.lower() == "warn":
            self.error_level = ct.ReportingLevel.WARNING
        else:
            self.error_level = ct.ReportingLevel.ERROR

        if args.simulate:
            self.combine = combiner.CombineMethod.SIMULATE
        else:
            self.combine = combiner.CombineMethod.NAIVE

        # boolean to enable/disable typechecking.
        self.typecheck = args.typecheck

        if args.typesused == 's' or args.typesused == 'simple':
            self.types_used = tv.TypesUsed.SIMPLE
        elif args.typesused == 'c' or args.typesused == 'complex':
            self.types_used = tv.TypesUsed.COMPLEX

        if args.target is not None:
            """
            The support_* flags are defaulted above,
            so we just toggle the necessary flags when
            necessary.
            """
            target = args.target.lower()
            if target == "m" or target == "mfsim":
                self.target = targets.TargetSelector.MFSIM
                if args.architecture != '':
                    self.architecture = args.architecture.lower()
                else:
                    self.architecture = None
                self.supports_functions = True
                self.supports_recursion = True
                self.supports_nesting = True
            elif target == 'i' or target == 'inkwell':
                self.target = targets.TargetSelector.INKWELL
                self.supports_functions = True
            elif target == "p" or target == "puddle":
                self.target = targets.TargetSelector.PUDDLE
                self.supports_functions = True
                self.supports_recursion = True
                self.supports_nesting = True
            elif target == "l" or target == 'llvm':
                self.target = targets.TargetSelector.LLVM_IR
                self.supports_functions = True
                self.supports_recursion = True
                self.supports_nesting = True
            else:
                self.target = targets.TargetSelector.IR
                self.supports_functions = True
                self.supports_recursion = True
                self.supports_nesting = True

        if args.library is not None:
            self.library = args.library

        if args.flow.lower() == 'active' or args.flow.lower() == 'a':
            self.flow_type = FlowType.ACTIVE

        if args.cdb:
            self.use_local_db = False

        if args.schema:
            self.schema = args.schema

        if args.validate:
            self.validate_schema = True

        if self.db['name'] and self.db['user'] and self.db['pass']:
            self.db_enabled = True
            if not self.db['addr']:
                self.db['addr'] = 'localhost'
            if not self.db['driver']:
                self.db['driver'] = 'mysql'
