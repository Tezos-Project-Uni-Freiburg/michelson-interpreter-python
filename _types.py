#!/usr/bin/python3
from copy import deepcopy
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any, Dict, List, Set


class CustomException(Exception):
    message: str
    extra_params: dict

    def __init__(self, message: str, extra_params: dict) -> None:
        super().__init__(message)
        self.extra_params = extra_params


@dataclass
class Data:
    prim: str = ""
    value: List = field(default_factory=list)
    parent: str | None = None
    name: str = ""
    attributes: List[str] = field(default_factory=list, init=False)

    def __post_init__(self) -> None:
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
        if self.name == "":
            self.name = create_variable(self.prim)
        CONCRETE_VARIABLES[self.name] = self
        SYMBOLIC_VARIABLES[self.name] = self.name + "_s"


@dataclass
class Delta:
    removed: List[Data] = field(default_factory=list)
    added: List[Data] = field(default_factory=list)


@dataclass
class State:
    account: str = ""
    address: str = ""
    amount: int = 0
    balance: int = 0
    entrypoint: str = "default"
    gas_limit: int = 0
    id: int = 0
    timestamp: int = int(datetime.now().timestamp())

    def __post_init__(self) -> None:
        self.balance += self.amount


@dataclass
class Step:
    delta: Delta
    instruction: List = field(default_factory=list)
    stack: List[Data] = field(default_factory=list)

    def __post_init__(self) -> None:
        self.stack = deepcopy(self.stack)


@dataclass
class PathConstraint:
    input_variables: Set[str] = field(default_factory=set)
    predicates: List[Any] = field(default_factory=list)
    is_processed: bool = False
    is_satisfiable: bool = False


VARIABLE_NAMES: Dict[str, Set[int]] = {}
CONCRETE_VARIABLES: Dict[str, Data] = {}
SYMBOLIC_VARIABLES: Dict[str, Any] = {}


def create_variable(name: str) -> str:
    n = 0
    if VARIABLE_NAMES.get(name):
        n = max(VARIABLE_NAMES[name]) + 1
        VARIABLE_NAMES[name].add(n)
    else:
        VARIABLE_NAMES[name] = {n}
    return name + "_" + str(n)
