from dataclasses import dataclass


class CustomException(Exception):
    ...


@dataclass
class Data:
    prim: str = ""
    value: list = []
    name: str = ""
    raw: dict = {}

    def __post_init__(self):
        if self.raw != {}:
            ...


@dataclass
class Delta:
    removed: list = []
    added: list = []


@dataclass
class State:
    account: str = ""
    address: str = ""
    amount: int = 0
    entrypoint: str = "default"
    gas_limit: int = 0
    id: int = 0
    timestamp: int = 0


@dataclass
class Step:
    delta: Delta
    instruction: list = []
    stack: list = []
