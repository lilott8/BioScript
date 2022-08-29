# import compiler.config.config as config
from compiler.config.config import Config
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
                                 default='ir', choices={'llvm', 'mfsim', 'puddle', 'inkwell', 'ir',
                                                        'l', 'm', 'p', 'i', 'ir'})
        self.parser.add_argument('-A,', '--architecture', help='Underlying architecture for DMFB (mfsim) targeting',
                                 type=str, default='')
        self.parser.add_argument('-cfg', '--write-cfg',
                                 help="Write the CFG to dot file", default=False, action='store_true')
        self.parser.add_argument('-inline', '--inline', help="Inline all, non-recursive functions", default=False,
                                 action='store_true')
        self.parser.add_argument('-stats', '--stats', help="Print the stats", default=False,
                                 action='store_true')

        self.parser.add_argument('-u', '--units', help="What does 1 unit equate to?", default="mL")

        self.parser.add_argument('-lu', '--loopunroll', help="Perform loop unrolling",
                                 default=False, action='store_true')

        self.parser.add_argument('-tv', '--track_volume', help="Perform volume tracking",
                                 default=False, action='store_true')

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

        inkwell_group = self.parser.add_argument_group('inkwell', "inkwell specific arguments:")
        inkwell_group.add_argument('-lib', '--library', help="Path to flat file of database.", default=None)
        inkwell_group.add_argument('-flow', '--flow', help="Which type of flow-based chip to target.",
                                   default="passive", choices={'active', 'a', 'passive', 'p'})
        inkwell_group.add_argument('--cdb', help="Name of Component Database", default='')
        inkwell_group.add_argument('--schema', help='The schema to validate json against.',
                                   default=None)
        inkwell_group.add_argument('--validate', help="Validate the schema is correct.", action='store_true')

        self.args = self.parser.parse_args(args)
        # This should always be the first instantiation of a Config.
        self.config = Config(self.args)
        self.validate_config()

        if self.config.debug:
            self.log.debug(self.config.input)

    def validate_config(self):
        if self.args.debug:
            self.log.debug('Running in debug mode')

        self.log.error("Don't forget to validate configs.")
