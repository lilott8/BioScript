from flow_synth.config.config import Config
from shared.base_cli import BaseCLI


class FlowSynthCLI(BaseCLI):

    def __init__(self, args):
        super().__init__(args)
        self.config = None

        self.parser.add_argument('-s', '--scheduler', help='What scheduler to use', type=str,
                                 default='list', choices={'list', 'path', 'priority', 'evo', 'ilp'})
        self.parser.add_argument('-r', '--router', help='What router to use', type=str,
                                 default='dijkstra_path', choices={'dijkstra_path', 'astar_path', 'bellman_ford_path'})
        self.parser.add_argument('-opt', '--optimize', help="Run optimizations?", type=bool, default=False)

        self.args = self.parser.parse_args(args)

        self.config = Config(self.args)
        self.validate_config()

        self.log.warning(self.config.input)

    def validate_config(self):
        if self.args.debug:
            self.log.info('Running in debug mode')

        self.log.error("Don't forget to validate configs.")
