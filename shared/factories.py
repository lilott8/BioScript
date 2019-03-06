from abc import abstractmethod, ABCMeta


class BaseFactory(metaclass=ABCMeta):

    @staticmethod
    @abstractmethod
    def get_object(name: str):
        raise NotImplemented
