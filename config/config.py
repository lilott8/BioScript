

class Config(object):

    config = None

    def __init__(self, args):
        Config.config = InternalConfig(args)

    @staticmethod
    def get_config(self, args):
        if Config.config is None:
            Config.config = InternalConfig(args)
            return Config.config
        else:
            return Config.config


class InternalConfig(object):

    def __init__(self, args):
        pass

