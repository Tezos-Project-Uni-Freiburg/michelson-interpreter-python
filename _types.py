#!/usr/bin/python3
from __future__ import annotations

from collections import deque
from copy import deepcopy
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any, Deque, Dict, List, Set

import z3

import _variables


class CustomException(Exception):
    def __init__(self, message: str, extra_params: dict = {}) -> None:
        super().__init__(message, extra_params)


@dataclass
class Data:
    prim: str = ""
    value: List = field(default_factory=list)
    parent: str | None = None
    name: str = ""
    attributes: List[str] = field(default_factory=list, init=False)
    # Datatype dependent optional attributes
    option_value: str = field(default_factory=str, init=False)
    option_type: List[str] = field(default_factory=list, init=False)
    contract_type: str = field(default_factory=str, init=False)
    key_type: str = field(default_factory=str, init=False)
    value_type: str = field(default_factory=str, init=False)
    set_type: str = field(default_factory=str, init=False)
    or_value: str = field(default_factory=str, init=False)
    or_type: List[str] = field(default_factory=list, init=False)
    list_type: str = field(default_factory=str, init=False)

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
            self.name = create_variable_name(self.prim)
        if _variables.CREATE_VARIABLE:
            _variables.CURRENT_RUN.concrete_variables[self.name] = self
            _variables.CURRENT_RUN.symbolic_variables[
                self.name
            ] = create_symbolic_variable(self)


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
    input_variables: Dict[str, z3.ExprRef] = field(default_factory=dict)
    predicates: List[Any] = field(default_factory=list)
    processed: bool = False
    satisfiable: bool = False
    reason: CustomException | None = field(default=None, init=False)


@dataclass
class Run:
    states: List[State] = field(default_factory=list)
    current_state: State = field(default_factory=State)
    stack: Deque[Data] = field(default_factory=deque)
    path_constraints: List[PathConstraint] = field(default_factory=list)
    current_path_constraint: PathConstraint = field(default_factory=PathConstraint)
    steps: List[Step] = field(default_factory=list)
    variable_names: Dict[str, Set[int]] = field(default_factory=dict)
    concrete_variables: Dict[str, Data] = field(default_factory=dict)
    symbolic_variables: Dict[str, z3.ExprRef] = field(default_factory=dict)
    ephemeral_variables: Dict[str, z3.ExprRef] = field(default_factory=dict, init=False)
    ephemeral_predicates: List[Any] = field(default_factory=list, init=False)
    creation_predicates: List[Any] = field(default_factory=list, init=False)
    executed: bool = field(default=False, init=False)


# VARIABLE_NAMES: Dict[str, Set[int]] = {}
# CONCRETE_VARIABLES: Dict[str, Data] = {}
# SYMBOLIC_VARIABLES: Dict[str, z3.ExprRef] = {}


def create_variable_name(name: str) -> str:
    n = 0
    if _variables.CURRENT_RUN.variable_names.get(name):
        n = max(_variables.CURRENT_RUN.variable_names[name]) + 1
        _variables.CURRENT_RUN.variable_names[name].add(n)
    else:
        _variables.CURRENT_RUN.variable_names[name] = {n}
    return name + "_" + str(n)


def create_symbolic_variable(d: Data) -> z3.ExprRef:
    match d.prim:
        case "int" | "mutez" | "nat" | "list" | "timestamp":
            return z3.Int(d.name)
        case (
            "address"
            | "bytes"
            | "chain_id"
            | "key"
            | "key_hash"
            | "signature"
            | "string"
        ):
            return z3.String(d.name)
        case "bool" | "or" | "option" | "pair" | "unit":
            return z3.Bool(d.name)
        case _:
            raise CustomException(
                "unknown sym var type " + d.prim,
                {"prim": d.prim, "value": d.value, "name": d.name},
            )
