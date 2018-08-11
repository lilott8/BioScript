import colorlog

class bslog(object):

    formatter = '%(log_color)s%(levelname)s:[%(name)s.%(funcName)s@%(lineno)s]:%(message)s'

    @staticmethod
    def getLogger(name: str):
        handler = colorlog.StreamHandler()
        handler.setFormatter(colorlog.ColoredFormatter(bslog.formatter))
        logger = colorlog.getLogger(name)
        logger.addHandler(handler)
        return logger
