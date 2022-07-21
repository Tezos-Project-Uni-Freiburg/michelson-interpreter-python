#!/usr/bin/python3

from functools import reduce
from hashlib import blake2b
from types import NoneType
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


def applyABS(instruction, parameters, stack) -> Data:
    return Data("nat", [str(abs(int(parameters[0].value[0])))])


def applyADD(instruction, parameters, stack) -> Data:
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


def applyADDRESS(instruction, parameters, stack):
    return parameters[0].value[0]


def applyAMOUNT(instruction, parameters, stack) -> Data:
    return Data("mutez", [str(globals()["CURRENT_STATE"].amount)])


def applyAND(instruction, parameters, stack) -> Data:
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


def applyAPPLY(instruction, parameters, stack) -> Data:
    # Not implemented
    return Data("lambda", [])


def applyBALANCE(instruction, parameters, stack) -> Data:
    return Data("mutez", [str(globals()["CURRENT_STATE"].amount)])


def applyBLAKE2B(instruction, parameters, stack) -> Data:
    return Data("bytes", [blake2b(bytes(parameters[0].value[0], "utf-8")).hexdigest()])


def applyCAR(instruction, parameters, stack):
    return parameters[0].value[0]


def applyCDR(instruction, parameters, stack):
    return parameters[0].value[0]


def applyCHAIN_ID(instruction, parameters, stack):
    # Not implemented
    return Data("chain_id", [""])


def applyCHECK_SIGNATURE(instruction, parameters, stack) -> Data:
    # Not implemented
    return Data("bool", ["False"])


def applyCOMPARE(instruction, parameters, stack) -> Data:
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


def applyCONCAT(instruction, parameters, stack) -> Data:
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


def applyCONS(instruction, parameters, stack):
    if parameters[0].prim != parameters[1].listType.prim:
        raise CustomException(
            "list type and element type are not same", [instruction, parameters]
        )
    else:
        parameters[1].value[0].insert(0, parameters[0])
        return parameters[1]


def applyCONTRACT(instruction, parameters, stack) -> Data:
    # Not implemented completely
    c = Data("contract", [parameters[0]])
    setattr(c, "contractType", instruction.args[0])
    output = Data("option", [c])
    setattr(output, "optionValue", "Some")
    setattr(output, "optionType", ["contract"])
    return output


def applyCREATE_CONTRACT(instruction, parameters, stack) -> List[Data]:
    # Not implemented
    return [Data("operation", []), Data("address", [])]


def applyDIG(instruction, parameters, stack) -> None:
    if instruction.args[0].int != 0:
        if instruction.args[0].int > stack.length - 1:
            raise CustomException(
                "not enough elements in the stack", [instruction, parameters]
            )
        arrayMoveMutable(
            stack, stack.length - 1 - instruction.args[0].int, stack.length - 1
        )
    return None


def apply(instruction, parameters, stack):
    # boilerplate instruction function
    ...


# from https://github.com/sindresorhus/array-move
# TODO: needs testing
def arrayMoveMutable(l: List, from_index: int, to_index: int) -> None:
    start_index = len(l) + from_index if from_index < 0 else from_index
    if start_index >= 0 and start_index < len(l):
        end_index = len(l) + to_index if to_index < 0 else to_index
        l.insert(end_index, l.pop(from_index))
