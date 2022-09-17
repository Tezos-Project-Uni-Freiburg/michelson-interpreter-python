#!/usr/bin/python3
from copy import deepcopy
from dataclasses import dataclass, field
from typing import Dict, List, Set
from venv import create

VARIABLES: Dict[str, Set[int]] = {}
REGENERATE_NAME: bool = False


def create_variable(name: str) -> str:
    n = 0
    if VARIABLES.get(name):
        n = max(VARIABLES[name]) + 1
        VARIABLES[name].add(n)
    else:
        VARIABLES[name] = {n}
    return name + "_" + str(n)


class CustomException(Exception):
    message: str
    extra_params: dict

    def __init__(self, message: str, extra_params: dict) -> None:
        super().__init__(message)
        self.extra_params = extra_params


@dataclass
class Data:
    prim: str = ""
    value: list = field(default_factory=list)
    name: str = ""
    raw: dict = field(default_factory=dict)
    attributes: list[str] = field(default_factory=list, init=False)

    def __post_init__(self) -> None:
        self.name = create_variable(self.prim)
        if self.raw != {}:
            ...
        match self.prim:
            case (
                "address"
                | "bool"
                | "bytes"
                | "chain_id"
                | "int"
                | "key"
                | "key_hash"
                | "mutez"
                | "nat"
                | "option"
                | "or"
                | "pair"
                | "signature"
                | "string"
                | "timestamp"
                | "unit"
            ):
                self.attributes = ["C", "PM", "S", "PU", "PA", "B", "D"]
            case "big_map":
                self.attributes = ["PM", "S", "D"]
            case "lambda" | "list" | "map" | "set":
                self.attributes = ["PM", "S", "PU", "PA", "B", "D"]
            case "contract":
                self.attributes = ["PM", "PA", "D"]
            case "operation":
                self.attributes = ["D"]
            case _:
                raise CustomException(
                    "unknown data type " + self.prim,
                    {"prim": self.prim, "value": self.value, "name": self.name},
                )
        if len(self.value) == 1 and self.value[0] is None:
            self.value[0] = ""

    def __deepcopy__(self, memo):
        # Taken from https://stackoverflow.com/a/15774013/5550674
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            setattr(result, k, deepcopy(v, memo))
        # Decide on name regeneration
        if REGENERATE_NAME:
            result.name = create_variable(result.prim)
        return result


@dataclass
class Delta:
    removed: List[Data] = field(default_factory=list)
    added: List[Data] = field(default_factory=list)


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
    instruction: list = field(default_factory=list)
    stack: list[Data] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.stack = deepcopy(self.stack)
