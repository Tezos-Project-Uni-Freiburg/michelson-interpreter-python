#!/usr/bin/python3
import copy
from dataclasses import dataclass, field


class CustomException(Exception):
    message: str
    extra_params: list

    def __init__(self, message: str, extra_params: list) -> None:
        super().__init__(message)
        self.extra_params = extra_params


@dataclass
class Data:
    prim: str = ""
    value: list = field(default_factory=list)
    name: str = ""
    raw: dict = field(default_factory=dict)
    attributes: set[str] = field(default_factory=set, init=False)

    def __post_init__(self) -> None:
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
                self.attributes.update({"C", "PM", "S", "PU", "PA", "B", "D"})
            case "big_map":
                self.attributes.update({"PM", "S", "D"})
            case "lambda" | "list" | "map" | "set":
                self.attributes.update({"PM", "S", "PU", "PA", "B", "D"})
            case "contract":
                self.attributes.update({"PM", "PA", "D"})
            case "operation":
                self.attributes.update({"D"})
            case _:
                raise CustomException(
                    "unknown data type " + self.prim, [self.prim, self.value, self.name]
                )
        if len(self.value) == 1 and self.value[0] is None:
            self.value[0] = ""


@dataclass
class Delta:
    removed: list[Data] = field(default_factory=list)
    added: list[Data] = field(default_factory=list)


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
        self.stack = copy.deepcopy(self.stack)
