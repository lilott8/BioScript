import storage.config.config as config
from shared.base_cli import BaseCLI


class ChemStorCLI(BaseCLI):
    """
    A CLI visitors class.
    Handles building the argsparser and validating the CLI arguments.
    This is the first class to build a config object.  It shouldn't be
    created before this point.
    """

    def __init__(self, args):
        super().__init__(args)
        self.config = None

        """
        Generic Parser Arguments
        """
        self.parser.add_argument('-validate', '--validate', help='Only validate a solution, don\'t provide a model.',
                                 default=False, action='store_true')
        self.parser.add_argument('-epa', '--epa-defs', help='Location of EPA definition file.', required=False,
                                 default='resources/epa.json')
        self.parser.add_argument('-abs', '--abs-int', help="Location for the abstract interaction files.",
                                 required=False, default='resources/abstract-interaction.txt')

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

    def validate_config(self):
        if self.args.debug:
            self.log.info('Running in debug mode')

        self.log.error("Don't forget to validate configs.")
