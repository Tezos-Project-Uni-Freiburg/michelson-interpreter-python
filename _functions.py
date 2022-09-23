#!/usr/bin/python3
import ast
import json
import re
from collections import deque
from copy import deepcopy
from datetime import datetime
from functools import reduce
from hashlib import blake2b, sha256, sha512
from math import trunc
from time import time
from typing import Any, Deque, Dict, List

from base58 import b58encode_check

import _types
import _variables
from _types import CustomException, Data, Delta, Step


def initialize(
    parameter_type: Dict[str, Any], parameter: str, storage_type: dict, storage: str
) -> Data:
    output = Data("pair", [])
    parameter_result: Data = globals()["parse" + parameter_type["prim"].upper()](
        parameter_type.get("args", []), parameter
    )
    setattr(parameter_result, "parent", output.name)
    storage_result: Data = globals()["parse" + storage_type["prim"].upper()](
        storage_type.get("args", []), storage
    )
    setattr(storage_result, "parent", output.name)
    output.value.extend([parameter_result, storage_result])
    return output


def get_instruction_parameters(
    requirements: Dict[str, Any], stack: Deque[Data]
) -> Deque[Data] | None:
    flag = False
    req_elems: Deque[Data] = deque()
    if requirements["multiple"]:
        req_size = len(
            reduce(
                lambda prev, cur: prev if len(prev) > len(cur) else cur,
                requirements["l"],
            )
        )
        if req_size > len(stack):
            raise CustomException(
                "not enough elements in the stack", {"requirements": requirements}
            )
        req_elems.extend(popmultiple(stack, req_size)[::-1])
        for i in range(len(requirements["l"])):
            temp = list(req_elems)[: len(requirements["l"][i])]
            if all(
                y == requirements["l"][i][x] or y is not None
                for x, y in enumerate(map(lambda x: x.prim, temp))
            ):
                flag = True
                return deque(temp)
        if not flag:
            raise CustomException(
                "stack elements and opcode req does not match",
                {"requirements": requirements},
            )
    elif requirements["l"][0] is None:
        return None
    else:
        req_size = len(requirements["l"])
        if req_size > len(stack):
            raise CustomException(
                "not enough elements in the stack", {"requirements": requirements}
            )
        req_elems: Deque[Data] = deque()
        req_elems.extend(popmultiple(stack, req_size)[::-1])
        if all(x == "SAME" for x in requirements["l"]):
            if len({x.prim for x in req_elems}) != 1:
                raise CustomException(
                    "top elements are not of same type", {"requirements": requirements}
                )
        elif all(len(x) > 0 for x in requirements["l"]) and not all(
            y == req_elems[x].prim for x, y in enumerate(requirements["l"])
        ):
            raise CustomException(
                "stack elements and opcode req does not match",
                {"requirements": requirements},
            )
    return req_elems


def get_instruction_requirements(instruction: str) -> Dict[str, bool | List[List[str]]]:
    requirements: Dict[str, Any] = {"multiple": False, "l": []}
    match instruction:
        case ("ABS" | "EQ" | "GE" | "GT" | "ISNAT" | "LE" | "LT" | "NEQ"):
            requirements["multiple"] = False
            requirements["l"].extend(["int"])
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
            requirements["l"].extend(["contract"])
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
            requirements["l"].extend([None])
        case "AND":
            requirements["multiple"] = True
            requirements["l"].extend([["bool", "bool"], ["nat", "nat"], ["int", "nat"]])
        case "BLAKE2B" | "SHA256" | "SHA512" | "UNPACK":
            requirements["multiple"] = False
            requirements["l"].extend(["bytes"])
        case "CAR" | "CDR":
            requirements["multiple"] = False
            requirements["l"].extend(["pair"])
        case "CHECK_SIGNATURE":
            requirements["multiple"] = False
            requirements["l"].extend(["key", "signature", "bytes"])
        case "CONCAT":
            # TODO: how to figure out that the type of list is either string or bytes?
            requirements["multiple"] = True
            requirements["l"].extend(
                [["string", "string"], ["bytes", "bytes"], ["list"]]
            )
        case "CONS":
            requirements["multiple"] = False
            requirements["l"].extend(["", "list"])
        case "CONTRACT":
            requirements["multiple"] = False
            requirements["l"].extend(["address"])
        case "EDIV":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    ["nat", "nat"],
                    ["nat", "int"],
                    ["int", "nat"],
                    ["int", "int"],
                    ["mutez", "nat"],
                    ["mutez", "mutez"],
                ]
            )
        case "EXEC":
            # TODO: how to determine ty1 and lambda's type match?
            requirements["multiple"] = False
            requirements["l"].extend(["", "lambda"])
        case "GET":
            requirements["multiple"] = True
            requirements["l"].extend([["", "map"], ["", "big_map"]])
        case "HASH_KEY":
            requirements["multiple"] = False
            requirements["l"].extend(["key"])
        case "IF":
            requirements["multiple"] = False
            requirements["l"].extend(["bool"])
        case "IF_CONS":
            requirements["multiple"] = False
            requirements["l"].extend(["list"])
        case "IF_LEFT":
            requirements["multiple"] = False
            requirements["l"].extend(["or"])
        case "IF_NONE" | "SET_DELEGATE":
            requirements["multiple"] = False
            requirements["l"].extend(["option"])
        case "IMPLICIT_ACCOUNT":
            requirements["multiple"] = False
            requirements["l"].extend(["key_hash"])
        case "INT":
            requirements["multiple"] = True  # TODO: check why is this True?
            requirements["l"].extend(["nat"])
        case "ITER":
            requirements["multiple"] = True
            requirements["l"].extend([["list"], ["set"], ["map"]])
        case "LSL" | "LSR":
            requirements["multiple"] = False
            requirements["l"].extend([["nat", "nat"]])
        case "MAP":
            requirements["multiple"] = True
            requirements["l"].extend([["list"], ["map"]])
        case "MEM":
            requirements["multiple"] = True
            requirements["l"].extend([["", "set"], ["", "map"], ["", "big_map"]])
        case "MUL":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    ["nat", "nat"],
                    ["nat", "int"],
                    ["int", "nat"],
                    ["int", "int"],
                    ["mutez", "nat"],
                    ["nat", "mutez"],
                ]
            )
        case "NEG":
            requirements["multiple"] = True
            requirements["l"].extend([["nat"], ["int"]])
        case "NOT":
            requirements["multiple"] = True
            requirements["l"].extend([["bool"], ["nat"], ["int"]])
        case "OR" | "XOR":
            requirements["multiple"] = True
            requirements["l"].extend([["bool", "bool"], ["nat", "nat"]])
        case "PACK" | "LEFT" | "RIGHT" | "SOME" | "SOURCE":  # TODO: how to determine ty1?
            requirements["multiple"] = False
            requirements["l"].extend([""])
        case "COMPARE":
            requirements["multiple"] = False
            requirements["l"].extend(["SAME", "SAME"])
        case "PAIR" | "SWAP":  # TODO: how to determine ty1 & ty2? && there's a PAIR n version now that's not represented here
            requirements["multiple"] = False
            requirements["l"].extend(["", ""])
        case "SIZE":
            requirements["multiple"] = True
            requirements["l"].extend(
                [["set"], ["map"], ["list"], ["string"], ["bytes"]]
            )
        case "SLICE":
            requirements["multiple"] = True
            requirements["l"].extend(
                [["nat", "nat", "string"], ["nat", "nat", "bytes"]]
            )
        case "SUB":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    ["nat", "nat"],
                    ["nat", "int"],
                    ["int", "nat"],
                    ["int", "int"],
                    ["timestamp", "int"],
                    ["timestamp", "timestamp"],
                    ["mutez", "mutez"],
                ]
            )
        case "TRANSFER_TOKENS":
            requirements["multiple"] = False
            requirements["l"].extend(["", "mutez", "contract"])
        case "UPDATE":
            requirements["multiple"] = True
            requirements["l"].extend(
                [
                    ["", "bool", "set"],
                    ["", "option", "map"],
                    ["", "option", "big_map"],
                ]
            )
        case _:
            raise CustomException("unknown instruction type " + instruction, {})
    return requirements


def process_instruction(
    instruction: Dict[str, Any], stack: Deque[Data], unpair_flag: bool = False
) -> Step:
    if "IF" in instruction["prim"]:
        _variables.STEPS.append(
            Step(Delta([], []), [instruction], list(deepcopy(stack)))
        )
    removed: List[Data] = []
    added: List[Data] = []
    parameters = get_instruction_parameters(
        get_instruction_requirements(instruction["prim"]), stack
    )
    if parameters is not None:
        removed.extend(deepcopy(parameters))
    _variables.UNPAIR_FLAG = unpair_flag
    result = globals()["apply" + instruction["prim"]](instruction, parameters, stack)
    _variables.UNPAIR_FLAG = False
    if result is not None:
        if not isinstance(result, list):
            if hasattr(result, "args") and not hasattr(result, "value"):
                result["value"] = result["args"]
                del result["args"]
            stack.append(result)
            added.append(result)
        else:
            for i in result[::-1]:
                if hasattr(i, "args") and not hasattr(i, "value"):
                    i["value"] = i["args"]
                    del i["args"]
                stack.append(i)
                added.append(i)
    return Step(Delta(removed, added), [instruction], list(deepcopy(stack)))


# instruction functions


def applyABS(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("nat", [str(abs(int(parameters[0].value[0])))])


def applyADD(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    value = [str(int(parameters[0].value[0]) + int(parameters[1].value[0]))]
    prim = ""
    match parameters[0].prim:
        case "nat":
            prim = "nat" if parameters[1].prim == "nat" else "int"
        case "int":
            prim = "timestamp" if parameters[1].prim == "timestamp" else "int"
        case "timestamp":
            prim = "timestamp"
        case "mutez":
            prim = "mutez"
        case _:
            raise CustomException(
                "unexpected prim in applyADD",
                {"instruction": instruction, "parameters": parameters},
            )
    return Data(prim, value)


def applyADDRESS(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
):
    return parameters[0].value[0]


def applyAMOUNT(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    return Data("mutez", [str(_variables.CURRENT_STATE.amount)])


def applyAND(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    match parameters[0].prim:
        case "bool":
            return Data(
                "bool",
                [
                    str(
                        parameters[0].value[0].lower() == "true"
                        and parameters[1].value[0].lower() == "true"
                    )
                ],
            )
        case "nat" | "int":
            return Data(
                "nat", [str(int(parameters[0].value[0]) & int(parameters[1].value[0]))]
            )
        case _:
            raise CustomException(
                "prim error in AND",
                {"instruction": instruction, "parameters": parameters},
            )


def applyAPPLY(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented
    return Data("lambda", [])


def applyBALANCE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    return Data("mutez", [str(_variables.CURRENT_STATE.amount)])


def applyBLAKE2B(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bytes", [blake2b(bytes(parameters[0].value[0], "utf-8")).hexdigest()])


def applyCAR(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    return parameters[0].value[0]


def applyCDR(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    return parameters[0].value[1]


def applyCHAIN_ID(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
):
    # Not implemented
    return Data("chain_id", [""])


def applyCHECK_SIGNATURE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented
    return Data("bool", ["False"])


def applyCOMPARE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # template
    if "C" not in parameters[0].attributes or "C" not in parameters[1].attributes:
        raise CustomException(
            "can't compare non-Comparable types",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("int", [])
    match parameters[0].prim:
        case "nat" | "int" | "mutez" | "timestamp":
            z1 = int(parameters[0].value[0])
            z2 = int(parameters[1].value[0])
            if z1 < z2:
                output.value.append("-1")
            elif z1 > z2:
                output.value.append("1")
            else:
                output.value.append("0")
        case (
            "address"
            | "string"
            | "bytes"
            | "key_hash"
            | "key"
            | "signature"
            | "chain_id"
        ):
            if parameters[0].value[0] < parameters[1].value[0]:
                output.value.append("-1")
            elif parameters[0].value[0] > parameters[1].value[0]:
                output.value.append("1")
            else:
                output.value.append("0")
        case _:
            raise CustomException(
                "COMPARE not implemented for complex types",
                {"instruction": instruction, "parameters": parameters},
            )
    return output


def applyCONCAT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    value = ""
    if parameters[0].prim != "list":
        value = parameters[0].value[0] + parameters[1].value[0]
        return Data("string" if parameters[0].prim == "string" else "bytes", [value])
    else:
        for i in parameters[0].value[0]:
            value += i.value[0]
        return Data(
            "string"
            if getattr(parameters[0], "listType").get("prim", None) == "string"
            else "bytes",
            [value],
        )


def applyCONS(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    if parameters[0].prim != getattr(parameters[1], "listType").get("prim", None):
        raise CustomException(
            "list type and element type are not same",
            {"instruction": instruction, "parameters": parameters},
        )
    else:
        parameters[1].value[0].insert(0, parameters[0])
        return parameters[1]


def applyCONTRACT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Not implemented completely
    output = Data("option", [])
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", ["contract"])
    c = Data("contract", [parameters[0]], output.name)
    setattr(c, "contractType", instruction["args"][0])
    output.value.append(c)
    return output


def applyCREATE_CONTRACT(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> List[Data]:
    # Not implemented
    return [Data("operation", []), Data("address", [])]


def applyDIG(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    if instruction["args"][0].int != 0:
        if instruction["args"][0].int > len(stack) - 1:
            raise CustomException(
                "not enough elements in the stack",
                {"instruction": instruction, "parameters": parameters},
            )
        dequemove(stack, len(stack) - 1 - instruction["args"][0].int, len(stack) - 1)
    return None


def applyDIP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    n = 1
    if "int" in instruction["args"][0]:
        n = int(instruction["args"][0]["int"])
        instruction["args"].pop(0)
        instruction["args"] = flatten(instruction["args"][0])
    if n + 1 > len(stack):
        raise CustomException(
            "not enough elements in stack",
            {"instruction": instruction, "parameters": parameters},
        )
    p: List[Data] = []
    for i in range(n):
        p.insert(0, stack.pop())
    for i in flatten(instruction["args"]):
        if isinstance(i, list):
            process_ifmacro(i)
        else:
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                _variables.STEPS.append(step)
    for i in p:
        stack.append(i)
    return None


def applyDROP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    n = int(instruction["args"][0].int) if "args" in instruction else 1
    if n > len(stack):
        raise CustomException(
            "not enough elements in the stack",
            {"instruction": instruction, "parameters": parameters},
        )
    if n != 0:
        for _ in range(n):
            stack.pop()
    return None


def applyDUG(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    n = int(instruction["args"][0].int)
    if n == 0:
        return None
    if n >= len(stack):
        raise CustomException(
            "not enough elements in the stack",
            {"instruction": instruction, "parameters": parameters},
        )
    stack.insert(len(stack) - 1 - n, stack[len(stack) - 1])
    stack.pop()
    return None


def applyDUP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    n = int(instruction["args"][0].int) if "args" in instruction else 1
    if n == 0:
        raise CustomException(
            "non-allowed value for " + instruction["prim"] + ": " + instruction["args"],
            {"instruction": instruction, "parameters": parameters},
        )
    if n > len(stack):
        raise CustomException(
            "not enough elements in the stack",
            {"instruction": instruction, "parameters": parameters},
        )
    # Kind of a lame solution but works ¯\_(ツ)_/¯
    _types.REGENERATE_NAME = not _variables.UNPAIR_FLAG
    output = deepcopy(stack[len(stack) - n])
    _types.REGENERATE_NAME = False
    return output


def applyEDIV(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    output = Data("option", [])
    setattr(output, "optionType", ["pair"])
    z1 = int(parameters[0].value[0])
    z2 = int(parameters[1].value[0])

    if z2 == 0:
        setattr(output, "optionValue", "None")
        return output
    else:
        setattr(output, "optionValue", "Some")

    q = trunc(z1 / z2)
    r = z1 % z2
    t1 = ""
    t2 = ""

    match parameters[0].prim:
        case "nat":
            if parameters[1].prim == "nat":
                t1 = "nat"
                t2 = "nat"
            else:
                t1 = "int"
                t2 = "nat"
        case "int":
            t1 = "int"
            t2 = "nat"
        case "mutez":
            if parameters[1].prim == "nat":
                t1 = "mutez"
            else:
                t1 = "nat"
            t2 = "mutez"
    p = Data("pair", [], output.name)
    p.value.extend([Data(t1, [str(q)], p.name), Data(t2, [str(r)], p.name)])
    output.value.append(p)
    return output


def applyEMPTY_BIG_MAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "C" not in Data(instruction["args"][0]["prim"]).attributes:
        raise CustomException(
            "kty is not comparable",
            {"instruction": instruction, "parameters": parameters},
        )
    elif {instruction["args"][1]["prim"]}.issubset({"operation", "big_map"}):
        raise CustomException(
            "vty is " + instruction["args"][1]["prim"],
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("big_map", [dict()])
    setattr(output, "keyType", instruction["args"][0])
    setattr(output, "valueType", instruction["args"][1])
    return output


def applyEMPTY_MAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "C" not in Data(instruction["args"][0]["prim"]).attributes:
        raise CustomException(
            "kty is not comparable",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("map", [dict()])
    setattr(output, "keyType", instruction["args"][0])
    setattr(output, "valueType", instruction["args"][1])
    return output


def applyEMPTY_SET(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "C" not in Data(instruction["args"][0]["prim"]).attributes:
        raise CustomException(
            "kty is not comparable",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("set", [set()])
    setattr(output, "setType", instruction["args"][0])
    return output


def applyEQ(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    result = Data("bool", [])
    if int(parameters[0].value[0]) == 0:
        result.value.append("True")
    else:
        result.value.append("False")
    return result


def applyEXEC(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented
    return Data("unit", [])


def applyFAILWITH(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    if "PA" not in stack[len(stack) - 1].attributes:
        raise CustomException(
            "FAILWITH got non-packable top element",
            {"instruction": instruction, "parameters": parameters},
        )
    else:
        raise CustomException(
            "got FAILWITH, top element of the stack: "
            + str(stack[len(stack) - 1].value),
            {"instruction": instruction, "parameters": parameters},
        )


def applyGE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) >= 0 else "False"])


def applyGET(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    output = Data("option", [])
    setattr(output, "optionType", [getattr(parameters[1], "keyType").prim])
    if parameters[0].value[0] in parameters[1].value[0]:
        setattr(output, "optionValue", "Some")
        output.value.append(parameters[1].value[0].get(parameters[0].value[0]))
    else:
        setattr(output, "optionValue", "None")
    return output


def applyGT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) > 0 else "False"])


def applyHASH_KEY(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data(
        "key_hash",
        [b58encode_check(bytes.fromhex(parameters[0].value[0])).decode("utf-8")],
    )


def applyIF(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    branch = 0 if parameters[0].value[0].lower() == "true" else 1
    for i in flatten(instruction["args"][branch]):
        if isinstance(i, list):
            process_ifmacro(i)
        else:
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                _variables.STEPS.append(step)
    return None


def applyIF_CONS(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    if len(parameters[0].value[0]) > 0:
        d = parameters[0].value[0].pop(0)
        stack.append(parameters[0])
        stack.append(d)
        branch = 0
    else:
        branch = 1
    for i in flatten(instruction["args"][branch]):
        if isinstance(i, list):
            process_ifmacro(i)
        else:
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                _variables.STEPS.append(step)
    return None


def applyIF_LEFT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    stack.append(parameters[0].value[0])
    branch = 0 if getattr(parameters[0], "orValue") == "Left" else 1
    for i in flatten(instruction["args"][branch]):
        if isinstance(i, list):
            process_ifmacro(i)
        else:
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                _variables.STEPS.append(step)
    return None


def applyIF_NONE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    if getattr(parameters[0], "optionValue") == "None":
        branch = 0
    else:
        branch = 1
        stack.append(parameters[0].value[0])
    for i in flatten(instruction["args"][branch]):
        if isinstance(i, list):
            process_ifmacro(i)
        else:
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                _variables.STEPS.append(step)
    return None


def applyIMPLICIT_ACCOUNT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    output = Data("contract", [parameters[0]])
    setattr(output, "contractType", Data("unit", ["Unit"], output.name))
    return output


def applyINT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("int", [parameters[0].value[0]])


def applyISNAT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    output = Data("option", [])
    setattr(output, "optionType", ["nat"])
    if int(parameters[0].value[0]) < 0:
        setattr(output, "optionValue", "None")
    else:
        setattr(output, "optionValue", "Some")
        output.value.append(Data("nat", [parameters[0].value[0]], output.name))
    return output


def applyITER(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> None:
    # Not implemented
    return None


def applyLAMBDA(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> None:
    # Not implemented
    return None


def applyLE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    result = Data("bool", [])
    if int(parameters[0].value[0]) <= 0:
        result.value.append("True")
    else:
        result.value.append("False")
    return result


def applyLEFT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    output = Data("or", [parameters[0]])
    setattr(output, "orValue", "Left")
    setattr(output, "orType", [parameters[0].prim, instruction["args"][0]["prim"]])
    return output


def applyLOOP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    top = stack.pop()
    v = False
    if top.prim != "bool":
        raise CustomException(
            "top element of stack is not bool",
            {"instruction": instruction, "parameters": parameters},
        )
    else:
        v = top.value[0].lower() == "true"
    while v:
        for i in flatten(instruction["args"]):
            if isinstance(i, list):
                process_ifmacro(i)
            else:
                step = process_instruction(i, stack)
                if "IF" not in i["prim"]:
                    _variables.STEPS.append(step)
        top = stack.pop()
        if top.prim != "bool":
            raise CustomException(
                "top element of stack is not bool",
                {"instruction": instruction, "parameters": parameters},
            )
        else:
            v = top.value[0].lower() == "true"
    return None


def applyLOOP_LEFT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    top = stack.pop()
    v = False
    if top.prim == "or":
        raise CustomException(
            "top element of stack is not or",
            {"instruction": instruction, "parameters": parameters},
        )
    elif getattr(top, "orValue") == "Right":
        stack.append(top)
        return None
    else:
        v = True
    while v:
        for i in flatten(instruction["args"]):
            if isinstance(i, list):
                process_ifmacro(i)
            else:
                step = process_instruction(i, stack)
                if "IF" not in i["prim"]:
                    _variables.STEPS.append(step)
        top = stack.pop()
        v = False
        if top.prim != "or":
            raise CustomException(
                "top element of stack is not or",
                {"instruction": instruction, "parameters": parameters},
            )
        elif getattr(top, "orValue") == "Right":
            stack.append(top)
            return None
        else:
            v = True
    return None


def applyLSL(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    f = int(parameters[0].value[0])
    s = int(parameters[1].value[0])
    if s > 256:
        raise CustomException(
            "s is larger than 256",
            {"instruction": instruction, "parameters": parameters},
        )
    return Data("nat", [str(f << s)])


def applyLSR(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    f = int(parameters[0].value[0])
    s = int(parameters[1].value[0])
    if s > 256:
        raise CustomException(
            "s is larger than 256",
            {"instruction": instruction, "parameters": parameters},
        )
    return Data("nat", [str(f >> s)])


def applyLT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) < 0 else "False"])


def applyMAP(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    new_list = []
    for _ in range(len(parameters[0].value[0])):
        stack.append(parameters[0].value[0].pop(0))
        for j in instruction["args"][::-1]:
            step = process_instruction(j, stack)
            if "IF" not in j.prim:
                _variables.STEPS.append(step)
        new_list.append(stack.pop())
    parameters[0].value[0] = new_list
    return parameters[0]


def applyMEM(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if (
        parameters[1].prim in ["big_map", "map"]
        and getattr(parameters[1], "keyType") != parameters[0].prim
    ) or getattr(parameters[1], "setType") != parameters[0].prim:
        raise CustomException(
            "key or element type does not match",
            {"instruction": instruction, "parameters": parameters},
        )
    return Data(
        "bool",
        ["True" if parameters[0].value[0] in parameters[1].value[0] else "False"],
    )


def applyMUL(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    z1 = int(parameters[0].value[0])
    z2 = int(parameters[1].value[0])
    t = ""

    match parameters[0].prim:
        case "nat":
            t = parameters[1].prim
        case "int":
            t = "int"
        case "mutez":
            t = "mutez"
    return Data(t, [str(z1 * z2)])


def applyNEG(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("int", [str(-int(parameters[0].value[0]))])


def applyNEQ(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) != 0 else "False"])


def applyNIL(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "args" not in instruction:
        raise CustomException(
            "type of list is not declared",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("list", [[]])
    setattr(output, "listType", instruction["args"][0])
    return output


def applyNONE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "args" not in instruction:
        raise CustomException(
            "type of option is not declared",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("option", [instruction["args"][0]["prim"]])
    setattr(output, "optionValue", "None")
    setattr(output, "optionType", instruction["args"])
    return output


def applyNOT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    match parameters[0].prim:
        case "int" | "nat":
            return Data("int", [str(~int(parameters[0].value[0]))])
        case "bool":
            return Data("bool", [str(parameters[0].value[0].lower() == "true")])
        case _:
            raise CustomException(
                "unknown prim", {"instruction": instruction, "parameters": parameters}
            )


def applyNOW(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    return Data("timestamp", [str(int(time() * 1000))])


def applyOR(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if parameters[0].prim == "bool":
        return Data(
            "bool",
            [
                str(
                    (parameters[0].value[0].lower()) == "true"
                    or (parameters[1].value[0].lower() == "true")
                )
            ],
        )
    else:
        return Data(
            "nat", [str(int(parameters[0].value[0]) | int(parameters[1].value[0]))]
        )


def applyPACK(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # not implemented
    if "PA" not in parameters[0].attributes:
        raise CustomException(
            "can't PACK non-packable type",
            {"instruction": instruction, "parameters": parameters},
        )
    return Data("bytes", [bytes(json.dumps(parameters[0].value), "utf-8").hex()])


def applyPAIR(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "args" in instruction:
        raise CustomException(
            "PAIR 'n' case hasn't been implemented",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("pair", [parameters[0], parameters[1]])
    parameters[0].parent = parameters[1].parent = output.name
    return output


def applyPUSH(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    output = Data(instruction["args"][0]["prim"], [])
    match instruction["args"][0]["prim"]:
        case "list":
            output.value.append([])
            setattr(output, "listType", instruction["args"][0]["args"][0])
            for i in range(1, len(instruction["args"])):
                v0 = Data(
                    getattr(output, "listType")["prim"],
                    [
                        instruction["args"][i]["int"]
                        or instruction["args"][i]["string"]
                        or instruction["args"][i]["bytes"]
                        or instruction["args"][i]["prim"]
                    ],
                    output.name,
                )
                output.value[0].append(v0)
        case "option":
            setattr(output, "optionValue", instruction["args"][1]["prim"])
            setattr(output, "optionType", [instruction["args"][0]["args"][0]])
            if getattr(output, "optionValue") != "None":
                v1 = Data(
                    getattr(output, "optionType")[0]["prim"],
                    [
                        instruction["args"][1]["args"][0]["int"]
                        or instruction["args"][1]["args"][0]["string"]
                        or instruction["args"][1]["args"][0]["bytes"]
                        or instruction["args"][1]["args"][0]["prim"]
                    ],
                    output.name,
                )
                output.value.append(v1)
        case "or":
            setattr(output, "orValue", instruction["args"][1]["prim"])
            setattr(output, "orType", instruction["args"][0]["args"])
            v2 = Data(
                getattr(output, "orType")[0]["prim"]
                if getattr(output, "orValue") == "Left"
                else getattr(output, "orType")[1]["prim"],
                [
                    instruction["args"][1]["args"][0]["int"]
                    or instruction["args"][1]["args"][0]["string"]
                    or instruction["args"][1]["args"][0]["bytes"]
                    or instruction["args"][1]["args"][0]["prim"]
                ],
                output.name,
            )
            output.value.append(v2)
        case _:
            value = (
                instruction["args"][1].get("int", None)
                or instruction["args"][1].get("string", None)
                or instruction["args"][1].get("bytes", None)
                or instruction["args"][1].get("prim", None)
            )
            output.value.append(value)
    return output


def applyRIGHT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    output = Data("or", [parameters[0]])
    parameters[0].parent = output.name
    setattr(output, "orValue", "Right")
    setattr(output, "orType", [instruction["args"][0]["prim"], parameters[0].prim])
    return output


def applySELF(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented completely
    output = Data("contract", [])
    setattr(output, "contractType", "Unit")
    output.value.append(
        Data("address", [_variables.CURRENT_STATE.address], output.name)
    )
    return output


def applySENDER(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented completely/correctly
    return Data("address", [_variables.CURRENT_STATE.address])


def applySET_DELEGATE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented
    return Data("operation", [])


def applySHA256(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bytes", [sha256(bytes(parameters[0].value[0])).hexdigest()])


def applySHA512(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("bytes", [sha512(bytes(parameters[0].value[0])).hexdigest()])


def applySIZE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    return Data("nat", [str(len(parameters[0].value[0]))])


def applySLICE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    offset = int(parameters[0].value[0])
    _len = int(parameters[1].value[0])
    _str = parameters[2].value[0]
    output = Data("option", [])
    setattr(output, "optionType", [parameters[2].prim])
    if len(_str) == 0 or offset >= len(_str) or offset + _len > len(_str):
        setattr(output, "optionValue", "None")
    elif offset < len(_str) and offset + _len <= len(_str):
        setattr(output, "optionValue", "Some")
        output.value.append(
            Data(parameters[2].prim, [_str[slice(offset, offset + _len)]], output.name)
        )
    return output


def applySOME(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "args" not in instruction:
        raise CustomException(
            "type of option is not declared",
            {"instruction": instruction, "parameters": parameters},
        )
    elif instruction["args"][0]["prim"] != parameters[0].prim:
        raise CustomException(
            "stack value and option type doesn't match",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("option", [parameters[0]])
    parameters[0].parent = output.name
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", [instruction["args"][0]["prim"]])
    return output


def applySOURCE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented completely
    return Data("address", [_variables.CURRENT_STATE.address])


def applySUB(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if "timestamp" in [parameters[0].prim, parameters[1].prim] and (
        re.match(r"[a-z]", parameters[0].value[0], flags=re.I)
        or re.match(r"[a-z]", parameters[1].value[0], flags=re.I)
    ):
        raise CustomException(
            "SUB not implemented for timestamps in RFC3339 notation",
            {"instruction": instruction, "parameters": parameters},
        )

    z1 = int(parameters[0].value[0])
    z2 = int(parameters[1].value[0])
    t = ""

    match parameters[0].prim:
        case "nat" | "int":
            t = "int"
        case "timestamp":
            t = "timestamp" if parameters[1].prim == "int" else "int"
        case "mutez":
            t = "mutez"

    return Data(t, [str(z1 - z2)])


def applySWAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> List:
    return list(parameters)[::-1]


def applyTRANSFER_TOKENS(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Not implemented
    return Data("operation", [])


def applyUNIT(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    return Data("unit", ["Unit"])


def applyUNPACK(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Type check is not being done here
    v = ast.literal_eval(
        json.dumps(bytes.fromhex(parameters[0].value[0]).decode("utf-8"))
    )
    output = Data("option", [])
    i = Data(instruction["args"][0]["prim"], [], output.name)
    # Don't know why this check is here
    if "args" in instruction["args"][0] and all(
        y == v[x].prim
        for x, y in enumerate(map(lambda x: x.prim, instruction["args"][0]["args"]))
    ):
        i.value = v
    else:
        i.value = v
    # Not implemented
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", [instruction["args"][0]["prim"]])
    output.value.append(i)
    return output


def applyUPDATE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
):
    # TODO: missing Data parent update
    if parameters[1].prim == "bool":
        if parameters[0].prim != getattr(parameters[2], "setType"):
            raise CustomException(
                "set type does not match",
                {"instruction": instruction, "parameters": parameters},
            )
        if parameters[1].value[0].lower() == "true":
            parameters[2].value[0].add(parameters[2].value)
        else:
            parameters[2].value[0].remove(parameters[2].value)
    else:
        if parameters[0].prim != getattr(parameters[2], "keyType"):
            raise CustomException(
                "key type does not match",
                {"instruction": instruction, "parameters": parameters},
            )
        if getattr(parameters[1], "optionValue") == "Some":
            if getattr(parameters[1], "optionType")[0] != getattr(
                parameters[2], "valueType"
            ):
                raise CustomException(
                    "value type does not match",
                    {"instruction": instruction, "parameters": parameters},
                )
            parameters[2].value[0][parameters[0].value[0]] = parameters[1]
        elif parameters[0].value[0] in parameters[2].value[0]:
            parameters[2].value[0].pop(parameters[0].value[0])
    return parameters[2]


def applyXOR(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    if parameters[0].prim == "bool":
        return Data(
            "bool",
            [str(parameters[0].value[0].lower() != parameters[1].value[0].lower())],
        )
    else:
        return Data(
            "nat", [str(int(parameters[0].value[0]) ^ int(parameters[1].value[0]))]
        )


def apply(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> None:
    # boilerplate instruction function
    ...


# instruction functions end


# parsing functions start
def parseADDRESS(args, value) -> Data:
    return Data("address", [re.sub(r'^"(.+(?="$))"$', r"\1", value)])


def parseBIG_MAP(args, value) -> Data:
    output = Data("big_map", [dict()])
    setattr(output, "keyType", args[0])
    setattr(output, "valueType", args[1])

    params = re.match(
        r"\s*\{\s*((?:Elt\s+.+\s+.+\s*;\s*)+(?:Elt\s+.+\s+.+\s*)?)\}\s*", value
    )
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    kv = [x.strip() for x in params[1].split(";")]
    if kv[len(kv) - 1] == "":
        kv.pop()
    for i in kv:
        r = re.match(r'Elt\s+([a-zA-Z0-9"_ ]+)\s+(.+)', i)
        if r is None:
            raise CustomException(
                "input doesn't match with the specified types",
                {"args": args, "value": value},
            )
        # r[1] is the key, and r[2] is the value
        match getattr(output, "keyType")["prim"]:
            case (
                "int" | "mutez" | "nat" | "timestamp" | "bytes" | "signature" | "bool"
            ):
                if r[1] in output.value[0]:
                    raise CustomException(
                        "key already present in map", {"args": args, "value": value}
                    )
            case ("string" | "address" | "key" | "key_hash"):
                if re.sub(r'^"(.+(?="$))"$', r"\1", r[1]) in output.value[0]:
                    raise CustomException(
                        "key already present in map", {"args": args, "value": value}
                    )
            case _:
                raise CustomException("not implemented", {"args": args, "value": value})
        output.value[0][r[1]] = globals()[
            "parse" + getattr(output, "valueType")["prim"].upper()
        ](args[1]["args"], r[2])
    return output


def parseBOOL(args, value) -> Data:
    return Data("bool", [value])


def parseBYTES(args, value) -> Data:
    r = re.match(r"0x([a-fA-F0-9]+)", value)
    if r is None:
        raise CustomException("can't parse", {"args": args, "value": value})
    return Data("bytes", [r[1]])


def parseINT(args, value) -> Data:
    return Data("int", [value])


def parseKEY(args, value) -> Data:
    return Data("key", [re.sub(r'^"(.+(?="$))"$', r"\1", value)])


def parseKEY_HASH(args, value) -> Data:
    return Data("key_hash", [re.sub(r'^"(.+(?="$))"$', r"\1", value)])


def parseLIST(args, value) -> Data:
    output = Data("list", [[]])
    setattr(output, "listType", args[0])

    params = re.match(r"\s*\{((?:.+\s*;)+(?:.+\s*)?)\s*\}\s*", value)
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    elements = [x.strip() for x in params[1].split(";")]
    if elements[len(elements) - 1] == "":
        elements.pop()
    for i in elements:
        v = globals()["parse" + getattr(output, "listType")["prim"].upper()](args[0], i)
        setattr(v, "parent", output.name)
        output.value[0].append(v)
    return output


def parseMAP(args, value) -> Data:
    output = Data("map", [dict()])
    setattr(output, "keyType", args[0])
    setattr(output, "valueType", args[1])

    params = re.match(
        r"\s*\{\s*((?:Elt\s+.+\s+.+\s*;\s*)+(?:Elt\s+.+\s+.+\s*)?)\}\s*", value
    )
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    kv = [x.strip() for x in params[1].split(";")]
    if kv[len(kv) - 1] == "":
        kv.pop()
    for i in kv:
        r = re.match(r'Elt\s+([a-zA-Z0-9"_ ]+)\s+(.+)', i)
        if r is None:
            raise CustomException(
                "input doesn't match with the specified types",
                {"args": args, "value": value},
            )
        # r[1] is the key, and r[2] is the value
        match getattr(output, "keyType")["prim"]:
            case (
                "int" | "mutez" | "nat" | "timestamp" | "bytes" | "signature" | "bool"
            ):
                if r[1] in output.value[0]:
                    raise CustomException(
                        "key already present in map", {"args": args, "value": value}
                    )
            case ("string" | "address" | "key" | "key_hash"):
                if re.sub(r'^"(.+(?="$))"$', r"\1", r[1]) in output.value[0]:
                    raise CustomException(
                        "key already present in map", {"args": args, "value": value}
                    )
            case _:
                raise CustomException("not implemented", {"args": args, "value": value})
        output.value[0][r[1]] = globals()[
            "parse" + getattr(output, "valueType")["prim"].upper()
        ](args[1]["args"], r[2])
    return output


def parseMUTEZ(args, value) -> Data:
    return Data("mutez", [value])


def parseNAT(args, value) -> Data:
    return Data("nat", [value])


def parseOPTION(args, value) -> Data:
    # Currently no parameter type check is being done
    output = Data("option", [])
    setattr(output, "optionType", [args[0]["prim"]])
    params = re.match(r"\s*\(\s*(?:(?:Some)\s+(.+)|(?:None)\s*)\s*\)\s*", value)
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    if "None" in params[0]:
        setattr(output, "optionValue", "None")
    else:
        setattr(output, "optionValue", "Some")
        v = globals()["parse" + getattr(output, "optionType")[0].upper()](
            args, params[1]
        )
        setattr(v, "parent", output.name)
        output.value.append(v)
    return output


def parseOR(args, value) -> Data:
    # Currently no parameter type check is being done
    params = re.match(r"\s*\(\s*(?:(Left|Right)\s+(.+))\s*\)\s*", value)
    output = Data("or", [])
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    setattr(output, "orValue", params[1])
    setattr(output, "orType", args)
    v = Data(
        getattr(output, "orType")[0]["prim"]
        if getattr(output, "orValue") == "Left"
        else getattr(output, "orType")[1]["prim"],
        [params[2]],
    )
    v.parent = output.name
    output.value.append(v)
    return output


def parsePAIR(args, value) -> Data:
    output = Data("pair", [])
    params = re.match(
        r"\s*\(\s*Pair\s+((?:\(.+\))|(?:.+?))\s+((?:\(.+\))|(?:.+?))\s*\)\s*", value
    )
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    v1 = globals()["parse" + args[0]["prim"].upper()](
        args[0].get("args", []), params[1]
    )
    setattr(v1, "parent", output.name)
    v2 = globals()["parse" + args[1]["prim"].upper()](
        args[1].get("args", []), params[2]
    )
    setattr(v2, "parent", output.name)
    output.value.extend([v1, v2])
    return output


def parseSET(args, value) -> Data:
    output = Data("set", [set()])
    setattr(output, "setType", args[0])

    params = re.match(r"\s*\{((?:.+\s*;)+(?:.+\s*)?)\s*\}\s*", value)
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    elements = [x.strip() for x in params[1].split(";")]
    if elements[len(elements) - 1] == "":
        elements.pop()
    for i in range(len(elements)):
        match getattr(output, "setType")["prim"]:
            case (
                "int" | "mutez" | "nat" | "timestamp" | "bytes" | "signature" | "bool"
            ):
                if elements[i] in output.value[0]:
                    raise CustomException(
                        "value already present in set", {"args": args, "value": value}
                    )
            case ("string" | "address" | "key" | "key_hash"):
                elements[i] = re.sub(r'^"(.+(?="$))"$', r"\1", elements[i])
                if elements[i] in output.value[0]:
                    raise CustomException(
                        "value already present in set", {"args": args, "value": value}
                    )
            case _:
                raise CustomException("not implemented", {"args": args, "value": value})
        output.value[0].add(elements[i])
    return output


def parseSIGNATURE(args, value) -> Data:
    # unfortunately no validation as of now
    return Data("signature", [value])


def parseSTRING(args, value) -> Data:
    return Data("string", [re.sub(r'^"(.+(?="$))"$', r"\1", value)])


def parseTIMESTAMP(args, value) -> Data:
    return Data(
        "timestamp",
        [
            str(
                (
                    datetime.fromisoformat(
                        re.sub(r'^"(.+(?="$))"$', r"\1", value)
                    ).timestamp()
                )
            )
            if re.match(r"[a-z]", value, flags=re.I)
            else str(value)
        ],
    )


def parseUNIT(args, value) -> Data:
    return Data("unit", ["Unit"])


def parse(args, value) -> Data:
    # boilerplate parsing function
    ...


# parsing functions end


# from https://github.com/sindresorhus/array-move
# TODO: needs testing
def dequemove(l: Deque, from_index: int, to_index: int) -> None:
    start_index = len(l) + from_index if from_index < 0 else from_index
    if start_index >= 0 and start_index < len(l):
        end_index = len(l) + to_index if to_index < 0 else to_index
        l.insert(end_index, popmultiple(l, from_index))


def flatten(l: List, skip_ifs: bool = True) -> List:
    o = []
    for i in l:
        if isinstance(i, list):
            if len(i) == 0:
                continue
            if skip_ifs and not isinstance(i[-1], list) and i[-1]["prim"] == "IF":
                o.append(i)
                continue
            for j in i:
                o.append(j)
        else:
            o.append(i)
    return o


def popmultiple(d: Deque, c: int) -> List:
    o = []
    for _ in range(c):
        o.append(d.pop())
    return o[::-1]


def process_ifmacro(l: List[Dict[str, Any]]) -> None:
    # TODO: definitely the most inefficient-looking part of the codebase
    CPC = _variables.CURRENT_PATH_CONSTRAINT
    op = _variables.OPS[l[1 if l[0]["prim"] == "COMPARE" else 0]["prim"]]
    CPC.initial_variables.append(_types.SYMBOLIC_VARIABLES[_variables.STACK[-1].name])
    # Some preprocessing
    if l[0]["prim"] == "COMPARE":
        CPC.initial_variables.append(
            _types.SYMBOLIC_VARIABLES[_variables.STACK[-2].name]
        )
        # Execute COMPARE here
        ins_c = l.pop(0)
        step = process_instruction(ins_c, _variables.STACK)
        if step is not None:
            _variables.STEPS.append(step)
    else:  # EQ, GE, etc...
        CPC.initial_variables.append("0")
    CPC.predicates.append(
        f"{CPC.initial_variables[-2]} {op} {CPC.initial_variables[-1]}"
    )
    if CPC.initial_variables[-1] == "0":
        _ = CPC.initial_variables.pop()
    ins_op, ins_if = l[0], l[1]
    # Execute EQ, GE, etc. here
    step = process_instruction(ins_op, _variables.STACK)
    if step is not None:
        _variables.STEPS.append(step)
    # Now we know which branch will be executed
    # negating & forking the current path constraint
    _variables.PATH_CONSTRAINTS.append(deepcopy(CPC))
    if _variables.STACK[-1].value[0].lower() == "true":
        # _variables.PATH_CONSTRAINTS[-1].predicates = [
        #     "!",
        #     _variables.PATH_CONSTRAINTS[-1].predicates,
        # ]
        _variables.PATH_CONSTRAINTS[-1].predicates.insert(
            len(_variables.PATH_CONSTRAINTS[-1].predicates) - 1, "!"
        )
    else:
        # CPC.predicates = ["!", CPC.predicates]
        CPC.predicates.insert(len(CPC.predicates) - 1, "!")
    # Now processing the actual IF
    _ = process_instruction(ins_if, _variables.STACK)


def process_unpairmacro(l: List[Dict[str, Any]]) -> None:
    # Process DUP
    dup = l.pop(0)
    step = process_instruction(dup, _variables.STACK, unpair_flag=True)
    if step is not None and "IF" not in dup["prim"]:
        _variables.STEPS.append(step)
    # Process the rest
    for i in flatten(l):
        step = process_instruction(i, _variables.STACK)
        if step is not None and "IF" not in i["prim"]:
            _variables.STEPS.append(step)
