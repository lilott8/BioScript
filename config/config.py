

class Config(object):

    config = None

    def __init__(self, args):
        Config.config = InternalConfig(args)

    @staticmethod
    def get_config(self):
        if self.config is None:
            Config.config = InternalConfig()
            return Config.config
        else:
            return Config.config


class InternalConfig(object):

    def __init__(self, args):
        parser = argparse.ArgumentParser()
        parser.add_argument('-d', '--debug', help='enable debug mode.')
        parser.add_argument('-s', '--simulate', help='Simulate chemistry.')
        parser.add_argument('-c', '--classify', help='Chemical classification level.', default=4)
        parser.add_argument('-l', '--level', help='What level to report errors at (warning or error).', default="error")
        parser.add_argument('-nf', '--no-filters', help="Disable smart filter creation", default=False)
        parser.add_argument('epa', '--epa-defs', help='Location of EPA definition file', default='./resources/epa.json')
        pass