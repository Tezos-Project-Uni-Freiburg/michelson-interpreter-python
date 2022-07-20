#!/usr/bin/python3

from dataclasses import dataclass, field


class CustomException(Exception):
    def __init__(self, message: str, extra_params: list) -> None:
        super().__init__(message)
        self.extra_params = extra_params


@dataclass
class Data:
    prim: str = ""
    value: list = field(default_factory=list)
    name: str = ""
    raw: dict = field(default_factory=dict)
    attributes: list = field(default_factory=list, init=False)

    def __post_init__(self):
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
                self.attributes.extend(["C", "PM", "S", "PU", "PA", "B", "D"])
            case "big_map":
                self.attributes.extend(["PM", "S", "D"])
            case "lambda" | "list" | "map" | "set":
                self.attributes.extend(["PM", "S", "PU", "PA", "B", "D"])
            case "contract":
                self.attributes.extend(["PM", "PA", "D"])
            case "operation":
                self.attributes.extend(["D"])
            case _:
                raise CustomException(
                    "unknown data type " + self.prim, [self.prim, self.value, self.name]
                )
        if len(self.value) == 1 and self.value[0] is None:
            self.value[0] = ""


@dataclass
class Delta:
    removed: list = field(default_factory=list)
    added: list = field(default_factory=list)


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
    stack: list = field(default_factory=list)
