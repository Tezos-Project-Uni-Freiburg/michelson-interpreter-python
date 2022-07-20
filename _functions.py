#!/usr/bin/python3

from functools import reduce
from typing import Any, Dict, List
from _types import CustomException, Data, Delta, State, Step


def initialize(
    parameter_type: Dict[str, Any], parameter: str, storage_type: dict, storage: str
) -> Data:
    parameter_result: Data = locals()["parse" + parameter_type["prim"].upper()](
        parameter_type["args"], parameter
    )
    storage_result: Data = locals()["parse" + storage_type["prim"].upper()](
        storage_type["args"], storage
    )
    return Data("pair", [parameter_result, storage_result])


def get_instruction_parameters(
    requirements: Dict[str, Any], stack: List[Data]
) -> List[Any]:
    flag = False
    if requirements["multiple"]:
        req_size = len(
            reduce(
                lambda prev, cur: prev if len(prev) > len(cur) else cur, requirements
            )
        )
        if req_size > len(stack):
            raise CustomException("not enough elements in the stack", [requirements])
        ...
    elif requirements["l"][0] is None:
        ...
    else:
        ...
    return []  # to suppress typing error for now


def get_instruction_requirements(instruction: str) -> Dict[str, bool | List[List[str]]]:
    requirements: Dict[str, Any] = {"multiple": False, "l": []}
    match instruction:
        case ("ABS" | "EQ" | "GE" | "GT" | "ISNAT" | "LE" | "LT" | "NEQ"):
            requirements["multiple"] = False
            requirements["l"].extend([["int"]])
        case "ADD":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    ["nat", "nat"],
                    ["nat", "int"],
                    ["int", "nat"],
                    ["int", "int"],
                    ["timestamp", "int"],
                    ["int", "timestamp"],
                    ["mutez", "mutez"],
                ]
            )
        case "ADDRESS":
            requirements["multiple"] = False
            requirements["l"].extend([["contract"]])
        case (
            "AMOUNT"
            | "APPLY"  # TODO: how to figure out ty1, ty2 and ty3?
            | "BALANCE"
            | "CHAIN_ID"
            | "CREATE_CONTRACT"  # TODO
            | "DIG"
            | "DIP"
            | "DROP"
            | "DUG"
            | "DUP"
            | "EMPTY_BIG_MAP"
            | "EMPTY_MAP"
            | "EMPTY_SET"
            | "FAILWITH"  # TODO: actually FAILWITH takes any type that's packable, need to figure out
            | "LAMBDA"
            | "LOOP"
            | "LOOP_LEFT"
            | "NIL"
            | "NONE"
            | "NOW"
            | "PUSH"
            | "SELF"
            | "SENDER"
            | "UNIT"
        ):
            requirements["multiple"] = False
            requirements["l"].extend([[None]])
        case "AND":
            requirements["multiple"] = True
            requirements["l"].extend(
                [[["bool", "bool"], ["nat", "nat"], ["int", "nat"]]]
            )
        case "BLAKE2B" | "SHA256" | "SHA512" | "UNPACK":
            requirements["multiple"] = False
            requirements["l"].extend([["bytes"]])
        case "CAR" | "CDR":
            requirements["multiple"] = False
            requirements["l"].extend([["pair"]])
        case "CHECK_SIGNATURE":
            requirements["multiple"] = False
            requirements["l"].extend([["key", "signature", "bytes"]])
        case "CONCAT":
            # TODO: how to figure out that the type of list is either string or bytes?
            requirements["multiple"] = True
            requirements["l"].extend(
                [[["string", "string"], ["bytes", "bytes"], ["list"]]]
            )
        case "CONS":
            requirements["multiple"] = False
            requirements["l"].extend([["", "list"]])
        case "CONTRACT":
            requirements["multiple"] = False
            requirements["l"].extend([["address"]])
        case "EDIV":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    [
                        ["nat", "nat"],
                        ["nat", "int"],
                        ["int", "nat"],
                        ["int", "int"],
                        ["mutez", "nat"],
                        ["mutez", "mutez"],
                    ]
                ]
            )
        case "EXEC":
            # TODO: how to determine ty1 and lambda's type match?
            requirements["multiple"] = False
            requirements["l"].extend([["", "lambda"]])
        case "GET":
            requirements["multiple"] = True
            requirements["l"].extend([[["", "map"], ["", "big_map"]]])
        case "HASH_KEY":
            requirements["multiple"] = False
            requirements["l"].extend([["key"]])
        case "IF":
            requirements["multiple"] = False
            requirements["l"].extend([["bool"]])
        case "IF_CONS":
            requirements["multiple"] = False
            requirements["l"].extend([["list"]])
        case "IF_LEFT":
            requirements["multiple"] = False
            requirements["l"].extend([["or"]])
        case "IF_NONE" | "SET_DELEGATE":
            requirements["multiple"] = False
            requirements["l"].extend([["option"]])
        case "IMPLICIT_ACCOUNT":
            requirements["multiple"] = False
            requirements["l"].extend([["key_hash"]])
        case "INT":
            requirements["multiple"] = True  # TODO: check why is this True?
            requirements["l"].extend([[["nat"]]])
        case "ITER":
            requirements["multiple"] = True
            requirements["l"].extend([[["list"], ["set"], ["map"]]])
        case "LSL" | "LSR":
            requirements["multiple"] = False
            requirements["l"].extend([["nat", "nat"]])
        case "MAP":
            requirements["multiple"] = True
            requirements["l"].extend([[["list"], ["map"]]])
        case "MEM":
            requirements["multiple"] = True
            requirements["l"].extend([[["", "set"], ["", "map"], ["", "big_map"]]])
        case "MUL":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    [
                        ["nat", "nat"],
                        ["nat", "int"],
                        ["int", "nat"],
                        ["int", "int"],
                        ["mutez", "nat"],
                        ["nat", "mutez"],
                    ]
                ]
            )
        case "NEG":
            requirements["multiple"] = True
            requirements["l"].extend([[["nat"], ["int"]]])
        case "NOT":
            requirements["multiple"] = True
            requirements["l"].extend([[["bool"], ["nat"], ["int"]]])
        case "OR" | "XOR":
            requirements["multiple"] = True
            requirements["l"].extend([[["bool", "bool"], ["nat", "nat"]]])
        case "PACK" | "LEFT" | "RIGHT" | "SOME" | "SOURCE":  # TODO: how to determine ty1?
            requirements["multiple"] = False
            requirements["l"].extend([[""]])
        case "COMPARE":
            requirements["multiple"] = False
            requirements["l"].extend([["SAME", "SAME"]])
        case "PAIR" | "SWAP":  # TODO: how to determine ty1 & ty2? && there's a PAIR n version now that's not represented here
            requirements["multiple"] = False
            requirements["l"].extend([["", ""]])
        case "SIZE":
            requirements["multiple"] = True
            requirements["l"].extend(
                [[["set"], ["map"], ["list"], ["string"], ["bytes"]]]
            )
        case "SLICE":
            requirements["multiple"] = True
            requirements["l"].extend(
                [[["nat", "nat", "string"], ["nat", "nat", "bytes"]]]
            )
        case "SUB":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    [
                        ["nat", "nat"],
                        ["nat", "int"],
                        ["int", "nat"],
                        ["int", "int"],
                        ["timestamp", "int"],
                        ["timestamp", "timestamp"],
                        ["mutez", "mutez"],
                    ]
                ]
            )
        case "TRANSFER_TOKENS":
            requirements["multiple"] = False
            requirements["l"].extend([["", "mutez", "contract"]])
        case "UPDATE":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    [
                        ["", "bool", "set"],
                        ["", "option", "map"],
                        ["", "option", "big_map"],
                    ]
                ]
            )
        case _:
            raise CustomException("unknown instruction type " + instruction, [])
    return requirements
