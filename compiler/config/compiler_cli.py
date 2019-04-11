import compiler.config.config as config
from shared.base_cli import BaseCLI


class CompilerCLI(BaseCLI):
    """
    A CLI visitors class.
    Handles building the argsparser and validating the CLI arguments.
    This is the first class to build a config object.  It shouldn't be
    created before this point.
    """

    def __init__(self, args):
        super().__init__(args)
        self.config = None

        self.parser.add_argument('-t', '--target', help='Platforms to target.', type=str,
                                 default='mfsim', choices={'llvm', 'mfsim', 'puddle', 'flow',
                                                           'l', 'm', 'p', 'i'})
        self.parser.add_argument('-cfg', '--write-cfg',
                                 help="Write the CFG to dot file", default=False, action='store_true')
        self.parser.add_argument('-inline', '--inline', help="Inline all, non-recursive functions", default=False,
                                 action='store_true')

        chemistry = self.parser.add_argument_group('chemistry', 'Chemistry specific arguments')
        chemistry.add_argument('-sim', '--simulate', help='Simulate chemistry.', default=False,
                               choices={True, False}, type=bool)
        chemistry.add_argument('-id', '--identify', help='Chemical identification level.', default=8,
                               choices={0, 1, 2, 4, 8, 16, 32}, type=int)
        chemistry.add_argument('-nf', '--no-filters', help='Disable smart filter creation.', action='store_true')
        chemistry.add_argument('-smarts', '--smarts', help='Length of smart filters to use.', default=5, type=int)

        typing_group = self.parser.add_argument_group('typing', 'Typing specific arguments')
        typing_group.add_argument('-tcl', '--typechecklevel', help='What level to report errors.', default="error",
                                  choices={'error', 'warn', 'none'})
        typing_group.add_argument('-tc', '--typecheck', help='Enable type checking input program.',
                                  action='store_true', default=False)
        typing_group.add_argument('-tcu', '--typesused', help='What types to use to typecheck a program.',
                                  choices={'s', 'simple', 'c', 'complex'}, default='s')
        typing_group.add_argument('-epa', '--epa-defs', help='Location of EPA definition file.', required=False,
                                  default='./resources/epa.json')
        typing_group.add_argument('-abs', '--abs-int', help="Location for the abstract interaction files.",
                                  required=False, default='./resources/abstract-interaction.txt')

        db_group = self.parser.add_argument_group('db', 'Database specific arguments:')
        db_group.add_argument('--dbname', help='Name of database.', default='')
        db_group.add_argument('--dbuser', help='Database user.')
        db_group.add_argument('--dbpass', help='Database password for user.')
        db_group.add_argument('--dbaddr', help='Address of database. [IP address | host name]', default='localhost')
        db_group.add_argument('--dbdriver', help='Database driver.', choices={'mysql', 'odbc'}, default='mysql')

        self.args = self.parser.parse_args(args)
        # This should always be the first instantiation of a Config.
        self.config = config.Config(self.args)
        self.validate_config()

        self.log.warning(self.config.input)

    def validate_config(self):
        if self.args.debug:
            self.log.info('Running in debug mode')

        self.log.error("Don't forget to validate configs.")
