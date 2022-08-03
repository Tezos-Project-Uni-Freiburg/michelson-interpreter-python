#!/usr/bin/python3

import ast
from copy import deepcopy
from functools import reduce
from hashlib import blake2b, sha256, sha512
import json
from math import trunc
import re
from time import time
from typing import Any, Dict, List

from base58 import b58encode_check

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
        req_elems = stack[-req_size:][::-1]
        for i in range(len(requirements["l"])):
            if all(
                y == requirements["l"][i][x] or y is not None
                for x, y in enumerate(
                    map(lambda x: x.prim, req_elems[: len(requirements["l"][i])])
                )
            ):
                flag = True
                return req_elems[: len(requirements["l"][i])]
        if not flag:
            raise CustomException(
                "stack elements and opcode req does not match", [requirements]
            )
    elif requirements["l"][0] is None:
        return [None]
    else:
        req_size = len(requirements["l"])
        if req_size > len(stack):
            raise CustomException("not enough elements in the stack", [requirements])
        req_elems = stack[-req_size:][::-1]
        if (
            all(x == "SAME" for x in requirements["l"])
            and len({x.prim for x in req_elems}) != 1
        ):
            raise CustomException("top elements are not of same type", [requirements])
        elif all(len(x) > 0 for x in requirements["l"]) and not all(
            y == req_elems[x].prim for x, y in enumerate(requirements["l"])
        ):
            raise CustomException(
                "stack elements and opcode req does not match", [requirements]
            )
    return req_elems


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


def process_instruction(
    instruction: Dict[Any, Any], stack: List[Data]
) -> Step | None:  # added `| None` to suppress typing error for now
    if "IF" in instruction["prim"]:
        globals()["STEPS"].append(Step(Delta([], []), [instruction], stack))
    removed: List[Data] = []
    added: List[Data] = []
    parameters = get_instruction_parameters(
        get_instruction_requirements(instruction["prim"]), stack
    )
    if len(parameters) != 1 or parameters[0] is not None:
        removed.extend(stack[-len(parameters) :][::-1])
        assert removed == parameters

    result = globals()["apply" + instruction["prim"]](instruction, parameters, stack)
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
    return Step(Delta(removed, added), [instruction], stack)


# instruction functions


def applyABS(instruction, parameters, stack: List[Data]) -> Data:
    return Data("nat", [str(abs(int(parameters[0].value[0])))])


def applyADD(instruction, parameters, stack: List[Data]) -> Data:
    output = Data("", [str(int(parameters[0].value[0]) + int(parameters[1].value[0]))])
    match parameters[0].prim:
        case "nat":
            output.prim = "nat" if parameters[1].prim is "nat" else "int"
        case "int":
            output.prim = "timestamp" if parameters[1].prim is "timestamp" else "int"
        case "timestamp":
            output.prim = "timestamp"
        case "mutez":
            output.prim = "mutez"
        case _:
            raise CustomException(
                "unexpected prim in applyADD", [instruction, parameters, stack]
            )
    return output


def applyADDRESS(instruction, parameters, stack: List[Data]):
    return parameters[0].value[0]


def applyAMOUNT(instruction, parameters, stack: List[Data]) -> Data:
    return Data("mutez", [str(globals()["CURRENT_STATE"].amount)])


def applyAND(instruction, parameters, stack: List[Data]) -> Data:
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
            raise CustomException("prim error in AND", [instruction, parameters])


def applyAPPLY(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented
    return Data("lambda", [])


def applyBALANCE(instruction, parameters, stack: List[Data]) -> Data:
    return Data("mutez", [str(globals()["CURRENT_STATE"].amount)])


def applyBLAKE2B(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bytes", [blake2b(bytes(parameters[0].value[0], "utf-8")).hexdigest()])


def applyCAR(instruction, parameters, stack: List[Data]):
    return parameters[0].value[0]


def applyCDR(instruction, parameters, stack: List[Data]):
    return parameters[0].value[0]


def applyCHAIN_ID(instruction, parameters, stack: List[Data]):
    # Not implemented
    return Data("chain_id", [""])


def applyCHECK_SIGNATURE(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented
    return Data("bool", ["False"])


def applyCOMPARE(instruction, parameters, stack: List[Data]) -> Data:
    # template
    if "C" not in parameters[0].attributes or "C" not in parameters[1].attributes:
        raise CustomException(
            "can't compare non-Comparable types", [instruction, parameters]
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
                "COMPARE not implemented for complex types", [instruction, parameters]
            )
    return output


def applyCONCAT(instruction, parameters, stack: List[Data]) -> Data:
    value = ""
    if parameters[0].prim != "list":
        value = parameters[0].value[0] + parameters[1].value[0]
        return Data("string" if parameters[0].prim == "string" else "bytes", [value])
    else:
        for i in parameters[0].value[0]:
            value += i.value[0]
        return Data(
            "string" if parameters[0].listType.prim == "string" else "bytes", [value]
        )


def applyCONS(instruction, parameters, stack: List[Data]):
    if parameters[0].prim != parameters[1].listType.prim:
        raise CustomException(
            "list type and element type are not same", [instruction, parameters]
        )
    else:
        parameters[1].value[0].insert(0, parameters[0])
        return parameters[1]


def applyCONTRACT(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented completely
    c = Data("contract", [parameters[0]])
    setattr(c, "contractType", instruction.args[0])
    output = Data("option", [c])
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", ["contract"])
    return output


def applyCREATE_CONTRACT(instruction, parameters, stack: List[Data]) -> List[Data]:
    # Not implemented
    return [Data("operation", []), Data("address", [])]


def applyDIG(instruction, parameters, stack: List[Data]) -> None:
    if instruction.args[0].int != 0:
        if instruction.args[0].int > len(stack) - 1:
            raise CustomException(
                "not enough elements in the stack", [instruction, parameters]
            )
        arrayMoveMutable(
            stack, len(stack) - 1 - instruction.args[0].int, len(stack) - 1
        )
    return None


def applyDIP(instruction, parameters, stack: List[Data]) -> None:
    n = 1
    if hasattr(instruction.args[0], "int"):
        n = int(instruction.args[0].int)
        instruction.args.pop(0)
    if n + 1 > len(stack):
        raise CustomException("not enough elements in stack", [instruction, parameters])
    p: List[Data] = []
    for i in range(n):
        p.insert(0, stack.pop())
    for i in [
        x for xs in instruction.args for x in xs
    ]:  # TODO: Test this JS Array.flat equivalent from
        # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
        step = process_instruction(i, stack)
        if "IF" not in i.prim:
            globals()["STEPS"].append(step)
    for i in p:
        stack.append(i)
    return None


def applyDROP(instruction, parameters, stack: List[Data]) -> None:
    n = int(instruction.args[0].int) if hasattr(instruction, "args") else 1
    if n > len(stack):
        raise CustomException(
            "not enough elements in the stack", [instruction, parameters]
        )
    if n != 0:
        for _ in range(n):
            stack.pop()
    return None


def applyDUG(instruction, parameters, stack: List[Data]) -> None:
    n = int(instruction.args[0].int)
    if n == 0:
        return None
    if n >= len(stack):
        raise CustomException(
            "not enough elements in the stack", [instruction, parameters]
        )
    stack.insert(len(stack) - 1 - n, stack[len(stack) - 1])
    stack.pop()
    return None


def applyDUP(instruction, parameters, stack: List[Data]) -> Data:
    n = int(instruction.args[0].int) if hasattr(instruction, "args") else 1
    if n == 0:
        raise CustomException(
            "non-allowed value for " + instruction.prim + ": " + instruction.args,
            [instruction, parameters],
        )
    if n > len(stack):
        raise CustomException(
            "not enough elements in the stack", [instruction, parameters]
        )
    return deepcopy(stack[len(stack) - n])


def applyEDIV(instruction, parameters, stack: List[Data]) -> Data:
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
    output.value.append(Data("pair", [Data(t1, [str(q)]), Data(t2, [str(r)])]))
    return output


def applyEMPTY_BIG_MAP(instruction, parameters, stack: List[Data]) -> Data:
    if "C" not in Data(instruction.args[0].prim).attributes:
        raise CustomException("kty is not comparable", [instruction, parameters])
    elif {instruction.args[1].prim}.issubset({"operation", "big_map"}):
        raise CustomException(
            "vty is " + instruction.args[1].prim, [instruction, parameters]
        )
    output = Data("big_map", [dict()])
    setattr(output, "keyType", instruction.args[0])
    setattr(output, "valueType", instruction.args[1])
    return output


def applyEMPTY_MAP(instruction, parameters, stack: List[Data]) -> Data:
    if "C" not in Data(instruction.args[0].prim).attributes:
        raise CustomException("kty is not comparable", [instruction, parameters])
    return Data("map", [instruction.args[0].prim, instruction.args[1].prim])


def applyEMPTY_SET(instruction, parameters, stack: List[Data]) -> Data:
    if "C" not in Data(instruction.args[0].prim).attributes:
        raise CustomException("kty is not comparable", [instruction, parameters])
    output = Data("set", [set()])
    setattr(output, "setType", instruction.args[0])
    return output


def applyEQ(instruction, parameters, stack: List[Data]) -> Data:
    result = Data("bool", [])
    if int(parameters[0].value[0]) == 0:
        result.value.append("True")
    else:
        result.value.append("False")
    return result


def applyEXEC(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented
    return Data("unit", [])


def applyFAILWITH(instruction, parameters, stack: List[Data]) -> None:
    if "PA" not in stack[len(stack) - 1].attributes:
        raise CustomException(
            "FAILWITH got non-packable top element", [instruction, parameters]
        )
    else:
        raise CustomException(
            "got FAILWITH, top element of the stack: "
            + str(stack[len(stack) - 1].value),
            [instruction, parameters],
        )


def applyGE(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) >= 0 else "False"])


def applyGET(instruction, parameters, stack: List[Data]) -> Data:
    output = Data("option", [])
    setattr(output, "optionType", [parameters[1].keyType.prim])
    if parameters[0].value[0] in parameters[1].value[0]:
        setattr(output, "optionValue", "Some")
        output.value.append(parameters[1].value[0].get(parameters[0].value[0]))
    else:
        setattr(output, "optionValue", "None")
    return output


def applyGT(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) > 0 else "False"])


def applyHASH_KEY(instruction, parameters, stack: List[Data]) -> Data:
    return Data(
        "key_hash",
        [b58encode_check(bytes.fromhex(parameters[0].value[0])).decode("utf-8")],
    )


def applyIF(instruction, parameters, stack: List[Data]) -> None:
    if parameters[0].value[0].lower() == "true":
        for i in [
            x for xs in instruction.args[0] for x in xs
        ]:  # TODO: Test this JS Array.flat equivalent from
            # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
            step = process_instruction(i, stack)
            if "IF" not in i.prim:
                globals()["STEPS"].append(step)
    else:
        for i in [
            x for xs in instruction.args[1] for x in xs
        ]:  # TODO: Test this JS Array.flat equivalent from
            # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
            step = process_instruction(i, stack)
            if "IF" not in i.prim:
                globals()["STEPS"].append(step)
    return None


def applyIF_CONS(instruction, parameters, stack: List[Data]) -> None:
    if len(parameters[0].value[0]) > 0:
        d = parameters[0].value[0].pop(0)
        stack.append(parameters[0])
        stack.append(d)
        branch = 0
    else:
        branch = 1
    for i in [
        x for xs in instruction.args[branch] for x in xs
    ]:  # TODO: Test this JS Array.flat equivalent from
        # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
        step = process_instruction(i, stack)
        if "IF" not in i.prim:
            globals()["STEPS"].append(step)
    return None


def applyIF_LEFT(instruction, parameters, stack: List[Data]) -> None:
    stack.append(parameters[0].value[0])
    branch = 0 if parameters[0].orValue == "Left" else 1
    for i in [
        x for xs in instruction.args[branch] for x in xs
    ]:  # TODO: Test this JS Array.flat equivalent from
        # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
        step = process_instruction(i, stack)
        if "IF" not in i.prim:
            globals()["STEPS"].append(step)
    return None


def applyIF_NONE(instruction, parameters, stack: List[Data]) -> None:
    if parameters[0].optionValue == "None":
        branch = 0
    else:
        branch = 1
        stack.append(parameters[0].value[0])
    for i in [
        x for xs in instruction.args[branch] for x in xs
    ]:  # TODO: Test this JS Array.flat equivalent from
        # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
        step = process_instruction(i, stack)
        if "IF" not in i.prim:
            globals()["STEPS"].append(step)
    return None


def applyIMPLICIT_ACCOUNT(instruction, parameters, stack: List[Data]) -> Data:
    output = Data("contract", [parameters[0]])
    setattr(output, "contractType", Data("unit", ["Unit"]))
    return output


def applyINT(instruction, parameters, stack: List[Data]) -> Data:
    return Data("int", [parameters[0].value[0]])


def applyISNAT(instruction, parameters, stack: List[Data]) -> Data:
    output = Data("option", [])
    setattr(output, "optionType", ["nat"])
    if int(parameters[0].value[0]) < 0:
        setattr(output, "optionValue", "None")
    else:
        setattr(output, "optionValue", "Some")
        output.value.append(Data("nat", [parameters[0].value[0]]))
    return output


def applyITER(instruction, parameters, stack: List[Data]) -> None:
    # Not implemented
    return None


def applyLAMBDA(instruction, parameters, stack: List[Data]) -> None:
    # Not implemented
    return None


def applyLE(instruction, parameters, stack: List[Data]) -> Data:
    result = Data("bool", [])
    if int(parameters[0].value[0]) <= 0:
        result.value.append("True")
    else:
        result.value.append("False")
    return result


def applyLEFT(instruction, parameters, stack: List[Data]) -> Data:
    output = Data("or", [parameters[0]])
    setattr(output, "orValue", "Left")
    setattr(output, "orType", [parameters[0].prim, instruction.args[0].prim])
    return output


def applyLOOP(instruction, parameters, stack: List[Data]) -> None:
    top = stack.pop()
    v = False
    if top.prim != "bool":
        raise CustomException(
            "top element of stack is not bool", [instruction, parameters]
        )
    else:
        v = top.value[0].lower() == "true"
    while v:
        for i in [
            x for xs in instruction.args for x in xs
        ]:  # TODO: Test this JS Array.flat equivalent from
            # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
            step = process_instruction(i, stack)
            if "IF" not in i.prim:
                globals()["STEPS"].append(step)
        top = stack.pop()
        if top.prim != "bool":
            raise CustomException(
                "top element of stack is not bool", [instruction, parameters]
            )
        else:
            v = top.value[0].lower() == "true"
    return None


def applyLOOP_LEFT(instruction, parameters, stack: List[Data]) -> None:
    top = stack.pop()
    v = False
    if top.prim == "or":
        raise CustomException(
            "top element of stack is not or", [instruction, parameters]
        )
    elif getattr(top, "orValue") == "Right":
        stack.append(top)
        return None
    else:
        v = True
    while v:
        for i in [
            x for xs in instruction.args for x in xs
        ]:  # TODO: Test this JS Array.flat equivalent from
            # https://stackoverflow.com/questions/952914/how-do-i-make-a-flat-list-out-of-a-list-of-lists
            step = process_instruction(i, stack)
            if "IF" not in i.prim:
                globals()["STEPS"].append(step)
        top = stack.pop()
        v = False
        if top.prim != "or":
            raise CustomException(
                "top element of stack is not or", [instruction, parameters]
            )
        elif getattr(top, "orValue") == "Right":
            stack.append(top)
            return None
        else:
            v = True
    return None


def applyLSL(instruction, parameters, stack: List[Data]) -> Data:
    f = int(parameters[0].value[0])
    s = int(parameters[1].value[0])
    if s > 256:
        raise CustomException("s is larger than 256", [instruction, parameters])
    return Data("nat", [str(f << s)])


def applyLSR(instruction, parameters, stack: List[Data]) -> Data:
    f = int(parameters[0].value[0])
    s = int(parameters[1].value[0])
    if s > 256:
        raise CustomException("s is larger than 256", [instruction, parameters])
    return Data("nat", [str(f >> s)])


def applyLT(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) < 0 else "False"])


def applyMAP(instruction, parameters, stack: List[Data]):
    new_list = []
    for _ in range(len(parameters[0].value[0])):
        stack.append(parameters[0].value[0].pop(0))
        for j in instruction.args[::-1]:
            step = process_instruction(j, stack)
            if "IF" not in j.prim:
                globals()["STEPS"].append(step)
        new_list.append(stack.pop())
    parameters[0].value[0] = new_list
    return parameters[0]


def applyMEM(instruction, parameters, stack: List[Data]) -> Data:
    if (
        parameters[1].prim in ["big_map", "map"]
        and parameters[1].keyType != parameters[0].prim
    ) or parameters[1].setType != parameters[0].prim:
        raise CustomException(
            "key or element type does not match", [instruction, parameters]
        )
    return Data(
        "bool",
        ["True" if parameters[0].value[0] in parameters[1].value[0] else "False"],
    )


def applyMUL(instruction, parameters, stack: List[Data]) -> Data:
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


def applyNEG(instruction, parameters, stack: List[Data]) -> Data:
    return Data("int", [str(-int(parameters[0].value[0]))])


def applyNEQ(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bool", ["True" if int(parameters[0].value[0]) != 0 else "False"])


def applyNIL(instruction, parameters, stack: List[Data]) -> Data:
    if not hasattr(instruction, "args"):
        raise CustomException("type of list is not declared", [instruction, parameters])
    output = Data("list", [[]])
    setattr(output, "listType", instruction.args[0])
    return output


def applyNONE(instruction, parameters, stack: List[Data]) -> Data:
    if not hasattr(instruction, "args"):
        raise CustomException(
            "type of option is not declared", [instruction, parameters]
        )
    output = Data("option", [instruction.args[0].prim])
    setattr(output, "optionValue", "None")
    setattr(output, "optionType", instruction.args)
    return output


def applyNOT(instruction, parameters, stack: List[Data]) -> Data:
    match parameters[0].prim:
        case "int" | "nat":
            return Data("int", [str(~int(parameters[0].value[0]))])
        case "bool":
            return Data("bool", [str(parameters[0].value[0].lower() == "true")])
        case _:
            raise CustomException("unknown prim", [instruction, parameters])


def applyNOW(instruction, parameters, stack: List[Data]) -> Data:
    return Data("timestamp", [str(int(time() * 1000))])


def applyOR(instruction, parameters, stack: List[Data]) -> Data:
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


def applyPACK(instruction, parameters, stack: List[Data]) -> Data:
    # not implemented
    if "PA" not in parameters[0].attributes:
        raise CustomException("can't PACK non-packable type", [instruction, parameters])
    return Data("bytes", [bytes(json.dumps(parameters[0].value), "utf-8").hex()])


def applyPAIR(instruction, parameters, stack: List[Data]) -> Data:
    if hasattr(instruction, "args"):
        raise CustomException(
            "PAIR 'n' case hasn't been implemented", [instruction, parameters]
        )
    return Data("pair", [parameters[0], parameters[1]])


def applyPUSH(instruction, parameters, stack: List[Data]) -> Data:
    output = Data(instruction.args[0].prim, [])
    match instruction.args[0].prim:
        case "list":
            output.value.append([])
            setattr(output, "listType", instruction.args[0].args[0])
            for i in range(1, len(instruction.args)):
                v0 = Data(
                    getattr(output, "listType").prim,
                    [
                        instruction.args[i].int
                        or instruction.args[i].string
                        or instruction.args[i].bytes
                        or instruction.args[i].prim
                    ],
                )
                output.value[0].append(v0)
        case "option":
            setattr(output, "optionValue", instruction.args[1].prim)
            setattr(output, "optionType", [instruction.args[0].args[0]])
            if getattr(output, "optionValue") != "None":
                v1 = Data(
                    getattr(output, "optionType")[0].prim,
                    [
                        instruction.args[1].args[0].int
                        or instruction.args[1].args[0].string
                        or instruction.args[1].args[0].bytes
                        or instruction.args[1].args[0].prim
                    ],
                )
                output.value.append(v1)
        case "or":
            setattr(output, "orValue", instruction.args[1].prim)
            setattr(output, "orType", instruction.args[0].args)
            v2 = Data(
                getattr(output, "orType")[0].prim
                if getattr(output, "orValue") == "Left"
                else getattr(output, "orType")[1].prim,
                [
                    instruction.args[1].args[0].int
                    or instruction.args[1].args[0].string
                    or instruction.args[1].args[0].bytes
                    or instruction.args[1].args[0].prim
                ],
            )
            output.value.append(v2)
        case _:
            value = (
                instruction.args[1].int
                or instruction.args[1].string
                or instruction.args[1].bytes
                or instruction.args[1].prim
            )
            output.value.append(value)
    return output


def applyRIGHT(instruction, parameters, stack: List[Data]) -> Data:
    output = Data("or", [parameters[0]])
    setattr(output, "orValue", "Right")
    setattr(output, "orType", [instruction.args[0].prim, parameters[0].prim])
    return output


def applySELF(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented completely
    output = Data("contract", [Data("address", [globals()["currentState"].address])])
    setattr(output, "contractType", "Unit")
    return output


def applySENDER(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented completely/correctly
    return Data("address", [globals()["currentState"].address])


def applySET_DELEGATE(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented
    return Data("operation", [])


def applySHA256(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bytes", [sha256(bytes(parameters[0].value[0])).hexdigest()])


def applySHA512(instruction, parameters, stack: List[Data]) -> Data:
    return Data("bytes", [sha512(bytes(parameters[0].value[0])).hexdigest()])


def applySIZE(instruction, parameters, stack: List[Data]) -> Data:
    return Data("nat", [str(len(parameters[0].value[0]))])


def applySLICE(instruction, parameters, stack: List[Data]) -> Data:
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
            Data(parameters[2].prim, [_str[slice(offset, offset + _len)]])
        )
    return output


def applySOME(instruction, parameters, stack: List[Data]) -> Data:
    if not hasattr(instruction, "args"):
        raise CustomException(
            "type of option is not declared", [instruction, parameters]
        )
    elif instruction.args[0].prim != parameters[0].prim:
        raise CustomException(
            "stack value and option type doesn't match", [instruction, parameters]
        )
    output = Data("option", [parameters[0]])
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", [instruction.args[0].prim])
    return output


def applySOURCE(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented completely
    return Data("address", [globals()["currentState"].address])


def applySUB(instruction, parameters, stack: List[Data]) -> Data:
    if "timestamp" in [parameters[0].prim, parameters[1].prim] and (
        re.match(r"[a-z]", parameters[0].value[0], flags=re.I)
        or re.match(r"[a-z]", parameters[1].value[0], flags=re.I)
    ):
        raise CustomException(
            "SUB not implemented for timestamps in RFC3339 notation",
            [instruction, parameters],
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


def applySWAP(instruction, parameters, stack: List[Data]) -> List:
    return parameters[::-1]


def applyTRANSFER_TOKENS(instruction, parameters, stack: List[Data]) -> Data:
    # Not implemented
    return Data("operation", [])


def applyUNIT(instruction, parameters, stack: List[Data]) -> Data:
    return Data("unit", ["Unit"])


def applyUNPACK(instruction, parameters, stack: List[Data]) -> Data:
    # Type check is not being done here
    v = ast.literal_eval(
        json.dumps(bytes.fromhex(parameters[0].value[0]).decode("utf-8"))
    )
    output = Data("option", [])
    i = Data(instruction.args[0].prim, [])
    # Don't know why this check is here
    if hasattr(instruction.args[0], "args") and all(
        y == v[x].prim
        for x, y in enumerate(map(lambda x: x.prim, instruction.args[0].args))
    ):
        i.value = v
    else:
        i.value = v
    # Not implemented
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", [instruction.args[0].prim])
    output.value.append(i)
    return output


def applyUPDATE(instruction, parameters, stack: List[Data]):
    if parameters[1].prim == "bool":
        if parameters[0].prim != parameters[2].setType:
            raise CustomException("set type does not match", [instruction, parameters])
        if parameters[1].value[0].lower() == "true":
            parameters[2].value[0].add(parameters[2].value)
        else:
            parameters[2].value[0].remove(parameters[2].value)
    else:
        if parameters[0].prim != parameters[2].keyType:
            raise CustomException("key type does not match", [instruction, parameters])
        if parameters[1].optionValue == "Some":
            if parameters[1].optionType[0] != parameters[2].valueType:
                raise CustomException(
                    "value type does not match", [instruction, parameters]
                )
            parameters[2].value[0][parameters[0].value[0]] = parameters[1]
        elif parameters[0].value[0] in parameters[2].value[0]:
            parameters[2].value[0].pop(parameters[0].value[0])
    return parameters[2]


def applyXOR(instruction, parameters, stack: List[Data]) -> Data:
    if parameters[0].prim == "bool":
        return Data(
            "bool",
            [str(parameters[0].value[0].lower() != parameters[1].value[0].lower())],
        )
    else:
        return Data(
            "nat", [str(int(parameters[0].value[0]) ^ int(parameters[1].value[0]))]
        )


# instruction functions end


def apply(instruction, parameters, stack: List[Data]) -> None:
    # boilerplate instruction function
    ...


# from https://github.com/sindresorhus/array-move
# TODO: needs testing
def arrayMoveMutable(l: List, from_index: int, to_index: int) -> None:
    start_index = len(l) + from_index if from_index < 0 else from_index
    if start_index >= 0 and start_index < len(l):
        end_index = len(l) + to_index if to_index < 0 else to_index
        l.insert(end_index, l.pop(from_index))
