#!/usr/bin/python3
from __future__ import annotations

import ast
import json
import operator
import re
from collections import deque
from copy import deepcopy
from datetime import datetime
from functools import reduce
from hashlib import blake2b, sha256, sha512
from math import trunc
from typing import Any, Deque, Dict, List

import z3
from base58 import b58encode_check

import _variables
from _types import CustomException, Data, Delta, Step, create_symbolic_variable


def initialize(
    parameter_type: Dict[str, Any], parameter: str, storage_type: dict, storage: str
) -> Data:
    output = Data("pair")
    parameter_result: Data = globals()["parse" + parameter_type["prim"].upper()](
        parameter_type.get("args", []), parameter
    )
    parameter_result.parent = output.name
    storage_result: Data = globals()["parse" + storage_type["prim"].upper()](
        storage_type.get("args", []), storage
    )
    storage_result.parent = output.name
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


def process_instruction(instruction: Dict[str, Any], stack: Deque[Data]) -> Step:
    if "IF" in instruction["prim"]:
        _variables.CURRENT_RUN.steps.append(
            Step(Delta([], []), [instruction], list(deepcopy(stack)))
        )
    removed: List[Data] = []
    added: List[Data] = []
    parameters = get_instruction_parameters(
        get_instruction_requirements(instruction["prim"]), stack
    )
    if parameters is not None:
        removed.extend(deepcopy(parameters))
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
    return Step(Delta(removed, added), [instruction], list(deepcopy(stack)))


# instruction functions


def applyABS(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  ABS  ::  int  :  A  ⇒  nat  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("nat", [str(abs(int(parameters[0].value[0])))])
    if parameters[0].name in CPC.input_variables:
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                CPC.input_variables[parameters[0].name],
            )
        )
    return output


def applyADD(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  ADD  ::  nat  :  nat  :  A  ⇒  nat  :  A
    # Γ  ⊢  ADD  ::  nat  :  int  :  A  ⇒  int  :  A
    # Γ  ⊢  ADD  ::  int  :  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  ADD  ::  int  :  int  :  A  ⇒  int  :  A
    # Γ  ⊢  ADD  ::  timestamp  :  int  :  A  ⇒  timestamp  :  A
    # Γ  ⊢  ADD  ::  int  :  timestamp  :  A  ⇒  timestamp  :  A
    # Γ  ⊢  ADD  ::  mutez  :  mutez  :  A  ⇒  mutez  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

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
    output = Data(prim, value)

    if set(CPC.input_variables.keys()) & set([i.name for i in parameters]):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                operator.add(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else parameters[0].value[0],
                    CPC.input_variables[parameters[1].name]
                    if parameters[1].name in CPC.input_variables
                    else parameters[1].value[0],
                ),
            )
        )
    return output


def applyADDRESS(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
):
    # Γ  ⊢  ADDRESS  ::  contract   ty1  :  A  ⇒  address  :  A
    return parameters[0].value[0]


def applyAMOUNT(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  AMOUNT  ::  A  ⇒  mutez  :  A
    output = Data(
        "mutez", [str(_variables.CURRENT_RUN.current_state.amount)], None, "sv_amount"
    )
    return output


def applyAND(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  AND  ::  bool  :  bool  :  A  ⇒  bool  :  A
    # Γ  ⊢  AND  ::  nat  :  nat  :  A  ⇒  nat  :  A
    # Γ  ⊢  AND  ::  int  :  nat  :  A  ⇒  nat  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    match parameters[0].prim:
        case "bool":
            output = Data(
                "bool",
                [
                    str(
                        parameters[0].value[0].lower() == "true"
                        and parameters[1].value[0].lower() == "true"
                    )
                ],
            )
            # For now, only implemented for bool
            if (
                set(CPC.input_variables.keys())
                | set(CR.ephemeral_symbolic_variables.keys())
            ) & set([i.name for i in parameters]):
                CR.ephemeral_concrete_variables[output.name] = output
                CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                    output
                )
                CR.temporary_predicates[output.name] = []
                if CR.temporary_predicates[parameters[0].name]:
                    CR.temporary_predicates[output.name].extend(
                        CR.temporary_predicates[parameters[0].name]
                    )
                if CR.temporary_predicates[parameters[1].name]:
                    CR.temporary_predicates[output.name].extend(
                        CR.temporary_predicates[parameters[1].name]
                    )
                op1 = (
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name]
                    if parameters[0].name in CR.ephemeral_symbolic_variables
                    else z3.BoolVal(parameters[0].value[0].lower() == "true")
                )
                op2 = (
                    CPC.input_variables[parameters[1].name]
                    if parameters[1].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[1].name]
                    if parameters[1].name in CR.ephemeral_symbolic_variables
                    else z3.BoolVal(parameters[1].value[0].lower() == "true")
                )
                CR.ephemeral_predicates.append(
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name], z3.And(op1, op2)
                    )
                )
            return output
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
    # Γ  ⊢  APPLY  ::  ty1  :  lambda   (  pair   ty1   ty2  )   ty3  :  A  ⇒  lambda   ty2   ty3  :  A
    # Not implemented
    return Data("lambda")


def applyBALANCE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  BALANCE  ::  A  ⇒  mutez  :  A
    return Data(
        "mutez", [str(_variables.CURRENT_RUN.current_state.balance)], None, "sv_balance"
    )


def applyBLAKE2B(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢   BLAKE2B   ::  bytes  :  A  ⇒  bytes  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data(
        "bytes", [blake2b(bytes(parameters[0].value[0], "utf-8")).hexdigest()]
    )
    if parameters[0].name in CPC.input_variables:
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                CPC.input_variables[parameters[0].name],
            )
        )
    return output


def applyCAR(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    # Γ  ⊢  CAR  ::  pair   ty1   ty2  :  A  ⇒  ty1  :  A
    return parameters[0].value[0]


def applyCDR(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    # Γ  ⊢  CDR  ::  pair   ty1   ty2  :  A  ⇒  ty2  :  A
    return parameters[0].value[1]


def applyCHAIN_ID(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
):
    # Γ  ⊢  CHAIN_ID  ::  A  ⇒  chain_id  :  A
    # Not implemented
    return Data("chain_id", ["0x1"], None, "sv_chain_id")


def applyCHECK_SIGNATURE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  CHECK_SIGNATURE  ::  key  :  signature  :  bytes  :  A  ⇒  bool  :  A
    # Not implemented
    return Data("bool", ["False"])


def applyCOMPARE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    #  z1  <  z2  COMPARE  /  z1  :  z2  :  S  ⇒  − 1   :  S
    #  z1  =  z2  COMPARE  /  z1  :  z2  :  S  ⇒  0  :  S
    #  z1  >  z2  COMPARE  /  z1  :  z2  :  S  ⇒  1  :  S
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    # template
    if "C" not in parameters[0].attributes or "C" not in parameters[1].attributes:
        raise CustomException(
            "can't compare non-Comparable types",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("int")
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
    if (
        set(CPC.input_variables.keys()) | set(CR.ephemeral_symbolic_variables.keys())
    ) & set([i.name for i in parameters]):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                z3.IntVal(output.value[0]),
            )
        )
        CR.conditional_operands[output.name] = (
            CPC.input_variables[parameters[0].name]
            if parameters[0].name in CPC.input_variables
            else CR.ephemeral_symbolic_variables[parameters[0].name]
            if parameters[0].name in CR.ephemeral_symbolic_variables
            else parameters[0].value[0],  # type: ignore
            CPC.input_variables[parameters[1].name]
            if parameters[1].name in CPC.input_variables
            else CR.ephemeral_symbolic_variables[parameters[1].name]
            if parameters[1].name in CR.ephemeral_symbolic_variables
            else parameters[1].value[0],  # type: ignore
        )
    return output


def applyCONCAT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  CONCAT  ::  string  :  string  :  A  ⇒  string  :  A
    # Γ  ⊢  CONCAT  ::  list   string  :  A  ⇒  string  :  A
    # Γ  ⊢  CONCAT  ::  bytes  :  bytes  :  A  ⇒  bytes  :  A
    # Γ  ⊢  CONCAT  ::  list   bytes  :  A  ⇒  bytes  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    value = ""
    if parameters[0].prim != "list":
        value = parameters[0].value[0] + parameters[1].value[0]
        output = Data("string" if parameters[0].prim == "string" else "bytes", [value])
    else:
        for i in parameters[0].value[0]:
            value += i.value[0]
        output = Data(
            "string" if parameters[0].list_type == "string" else "bytes",
            [value],
        )
        # Only implemented for literal concats for now
        if set(CPC.input_variables.keys()) & set([i.name for i in parameters]):
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[output.name],
                    operator.add(
                        CPC.input_variables[parameters[0].name]
                        if parameters[0].name in CPC.input_variables
                        else parameters[0].value[0],
                        CPC.input_variables[parameters[1].name]
                        if parameters[1].name in CPC.input_variables
                        else parameters[1].value[0],
                    ),
                )
            )
    return output


def applyCONS(instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]):
    # Γ  ⊢  CONS  ::  ty1  :  list   ty1  :  A  ⇒  list   ty1  :  A
    if parameters[0].prim != parameters[1].list_type:
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
    # Γ  ⊢  CONTRACT   ty  ::  address  :  A  ⇒  option   (  contract   ty  )  :  A
    # Not implemented completely
    output = Data("option")
    output.option_value = "Some"
    output.option_type.append("contract")
    c = Data("contract", [parameters[0]], output.name)
    c.contract_type = instruction["args"][0].get("prim")
    output.value.append(c)
    return output


def applyCREATE_CONTRACT(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> List[Data]:
    # Some ty2  ⊢  instr  ::  pair   ty2   ty1  :   [ ]   ⇒  pair   (  list   operation  )   ty1  :   [ ]
    # Γ  ⊢  CREATE_CONTRACT   {   parameter   ty1  ;   storage   ty2  ;   code   instr1  }  ::  option   key_hash  :  mutez  :  ty2  :  A  ⇒  operation  :  address  :  A
    # Not implemented
    return [Data("operation"), Data("address")]


def applyDIG(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  DIG   n  ::  A  @  (  ty1  :  B  )  ⇒  ty1  :  (  A  @  B  )
    if instruction["args"][0]["int"] != "0":
        if int(instruction["args"][0]["int"]) > len(stack) - 1:
            raise CustomException(
                "not enough elements in the stack",
                {"instruction": instruction, "parameters": parameters},
            )
        e = stack[len(stack) - 1 - int(instruction["args"][0]["int"])]
        stack.remove(e)
        stack.append(e)
    return None


def applyDIP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    #  Γ  ⊢  DIP   instr  ::  ty  :  B  ⇒  ty  :  C
    n = 1
    if "int" in instruction["args"][0]:
        n = int(instruction["args"][0]["int"])
        instruction["args"].pop(0)
        instruction["args"] = flatten(instruction["args"][0])
    if n > len(stack):
        raise CustomException(
            "not enough elements in stack",
            {"instruction": instruction, "parameters": parameters},
        )
    p: List[Data] = []
    for i in range(n):
        p.insert(0, stack.pop())
    for i in flatten(instruction["args"]):
        step = process_instruction(i, stack)
        if "IF" not in i["prim"]:
            _variables.CURRENT_RUN.steps.append(step)
    for i in p:
        stack.append(i)
    return None


def applyDROP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  DROP  ::  ty  :  A  ⇒  A
    n = int(instruction["args"][0]["int"]) if "args" in instruction else 1
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
    # Γ  ⊢  DUG   n  ::  ty1  :  (  A  @  B  )  ⇒  A  @  (  ty1  :  B  )
    n = int(instruction["args"][0]["int"])
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
    # Γ  ⊢  DUP  ::  ty1  :  A  ⇒  ty1  :  ty1  :  A
    n = int(instruction["args"][0]["int"]) if "args" in instruction else 1
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
    output = deepcopy(stack[len(stack) - n])
    return output


def applyEDIV(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  EDIV  ::  nat  :  nat  :  A  ⇒  option   (  pair   nat   nat  )  :  A
    # Γ  ⊢  EDIV  ::  nat  :  int  :  A  ⇒  option   (  pair   int   nat  )  :  A
    # Γ  ⊢  EDIV  ::  int  :  nat  :  A  ⇒  option   (  pair   int   nat  )  :  A
    # Γ  ⊢  EDIV  ::  int  :  int  :  A  ⇒  option   (  pair   int   nat  )  :  A
    # Γ  ⊢  EDIV  ::  mutez  :  nat  :  A  ⇒  option   (  pair   mutez   mutez  )  :  A
    # Γ  ⊢  EDIV  ::  mutez  :  mutez  :  A  ⇒  option   (  pair   nat   mutez  )  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    output = Data("option")
    output.option_type.append("pair")
    z1 = int(parameters[0].value[0])
    z2 = int(parameters[1].value[0])

    if z2 == 0:
        output.option_value = "None"
        if parameters[1].name in CPC.input_variables | CR.ephemeral_symbolic_variables:
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[output.name],
                    (
                        operator.eq(
                            CPC.input_variables[parameters[1].name], z3.IntVal(0)
                        )
                    ),
                )
            )
        return output
    else:
        output.option_value = "Some"

    s = z3.Solver()
    z1_s, z2_s, q_s, r_s = z3.Ints("z1 z2 q r")
    s.add(
        q_s == z1_s / z2_s,
        r_s == z1_s % z2_s,
        z1_s == (q_s * z2_s) + r_s,
        z1_s == z3.IntVal(z1),
        z2_s == z3.IntVal(z2),
    )
    if s.check() == z3.sat:
        q = s.model()[q_s].as_long()  # type: ignore
        r = s.model()[r_s].as_long()  # type: ignore
        s.reset()
    else:
        # These can be wrong, EDIV logic is weird
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
    q_p = Data(t1, [str(q)], p.name)
    r_p = Data(t2, [str(r)], p.name)
    p.value.extend([q_p, r_p])
    output.value.append(p)
    if set(CPC.input_variables.keys()) & set([i.name for i in parameters]):
        CR.ephemeral_concrete_variables[p.name] = p
        CR.ephemeral_symbolic_variables[p.name] = create_symbolic_variable(p)
        if parameters[1].name in CPC.input_variables:
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.ephemeral_predicates.extend(
                [
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name],
                        (
                            operator.ne(
                                CPC.input_variables[parameters[1].name], z3.IntVal(0)
                            )
                        ),
                    ),
                    operator.eq(
                        CR.ephemeral_symbolic_variables[p.name],
                        CR.ephemeral_symbolic_variables[output.name],
                    ),
                ]
            )
        else:
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[p.name],
                    z3.BoolVal(True),
                )
            )
        CR.ephemeral_concrete_variables[q_p.name] = q_p
        CR.ephemeral_symbolic_variables[q_p.name] = create_symbolic_variable(q_p)
        CR.ephemeral_concrete_variables[r_p.name] = r_p
        CR.ephemeral_symbolic_variables[r_p.name] = create_symbolic_variable(r_p)
        CR.ephemeral_predicates.extend(
            [
                operator.eq(
                    CR.ephemeral_symbolic_variables[q_p.name],
                    operator.truediv(
                        CPC.input_variables[parameters[0].name]
                        if parameters[0].name in CPC.input_variables
                        else z3.IntVal(int(parameters[0].value[0])),
                        CPC.input_variables[parameters[1].name]
                        if parameters[1].name in CPC.input_variables
                        else z3.IntVal(int(parameters[1].value[0])),
                    ),
                ),
                operator.eq(
                    CR.ephemeral_symbolic_variables[r_p.name],
                    operator.mod(
                        CPC.input_variables[parameters[0].name]
                        if parameters[0].name in CPC.input_variables
                        else z3.IntVal(int(parameters[0].value[0])),
                        CPC.input_variables[parameters[1].name]
                        if parameters[1].name in CPC.input_variables
                        else z3.IntVal(int(parameters[1].value[0])),
                    ),
                ),
                operator.eq(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else z3.IntVal(int(parameters[0].value[0])),
                    operator.add(
                        operator.mul(
                            CR.ephemeral_symbolic_variables[q_p.name],
                            CPC.input_variables[parameters[1].name]
                            if parameters[1].name in CPC.input_variables
                            else z3.IntVal(int(parameters[1].value[0])),
                        ),
                        CR.ephemeral_symbolic_variables[r_p.name],
                    ),
                ),
            ]
        )
    return output


def applyEMPTY_BIG_MAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  EMPTY_BIG_MAP   kty   vty  ::  A  ⇒  big_map   kty   vty  :  A
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
    output.key_type = instruction["args"][0].get("prim")
    output.value_type = instruction["args"][1].get("prim")
    return output


def applyEMPTY_MAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  EMPTY_MAP   kty   vty  ::  A  ⇒  map   kty   vty  :  A
    if "C" not in Data(instruction["args"][0]["prim"]).attributes:
        raise CustomException(
            "kty is not comparable",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("map", [dict()])
    output.key_type = instruction["args"][0].get("prim")
    output.value_type = instruction["args"][1].get("prim")
    return output


def applyEMPTY_SET(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  EMPTY_SET   cty  ::  A  ⇒  set   cty  :  A
    if "C" not in Data(instruction["args"][0]["prim"]).attributes:
        raise CustomException(
            "kty is not comparable",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("set", [set()])
    output.set_type = instruction["args"][0].get("prim")
    return output


def applyEQ(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  EQ  ::  int  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("bool")
    if int(parameters[0].value[0]) == 0:
        output.value.append("True")
    else:
        output.value.append("False")
    if (
        parameters[0].name in CPC.input_variables
        or parameters[0].name in CR.ephemeral_symbolic_variables
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if CR.conditional_operands.get(parameters[0].name):
            CR.temporary_predicates[output.name] = [
                operator.eq(
                    CR.conditional_operands[parameters[0].name][0],
                    CR.conditional_operands[parameters[0].name][1],
                )
            ]
        elif (
            CR.temporary_predicates[parameters[0].name]
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CR.temporary_predicates[output.name] = CR.temporary_predicates[
                parameters[0].name
            ]
        else:
            CR.temporary_predicates[output.name] = []
        op = operator.eq if output.value[0].lower() == "true" else operator.ne
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                op(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name],
                    z3.IntVal(0),
                ),
            )
        )
    return output


def applyEXEC(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  EXEC  ::  ty1  :  lambda   ty1   ty2  :  A  ⇒  ty2  :  A
    # Not implemented
    return Data("unit", ["Unit"])


def applyFAILWITH(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  FAILWITH  ::  ty1  :  A  ⇒  B
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
    # Γ  ⊢  GE  ::  int  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("bool")
    if int(parameters[0].value[0]) >= 0:
        output.value.append("True")
    else:
        output.value.append("False")
    if (
        parameters[0].name in CPC.input_variables
        or parameters[0].name in CR.ephemeral_symbolic_variables
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if CR.conditional_operands.get(parameters[0].name):
            CR.temporary_predicates[output.name] = [
                operator.ge(
                    CR.conditional_operands[parameters[0].name][0],  # type: ignore
                    CR.conditional_operands[parameters[0].name][1],  # type: ignore
                )
            ]
        elif (
            CR.temporary_predicates[parameters[0].name]
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CR.temporary_predicates[output.name] = CR.temporary_predicates[
                parameters[0].name
            ]
        else:
            CR.temporary_predicates[output.name] = []
        op = operator.ge if output.value[0].lower() == "true" else operator.lt
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                op(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name],  # type: ignore
                    z3.IntVal(0),
                ),
            )
        )
    return output


def applyGET(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  GET  ::  kty  :  map   kty   vty  :  A  ⇒  option   vty  :  A
    # Γ  ⊢  GET  ::  kty  :  big_map   kty   vty  :  A  ⇒  option   vty  :  A
    output = Data("option")
    output.option_type.append(parameters[1].key_type)
    if parameters[0].value[0] in parameters[1].value[0]:
        output.option_value = "Some"
        output.value.append(parameters[1].value[0].get(parameters[0].value[0]))
    else:
        output.option_value = "None"
    return output


def applyGT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  GT  ::  int  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("bool")
    if int(parameters[0].value[0]) > 0:
        output.value.append("True")
    else:
        output.value.append("False")
    if (
        parameters[0].name in CPC.input_variables
        or parameters[0].name in CR.ephemeral_symbolic_variables
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if CR.conditional_operands.get(parameters[0].name):
            CR.temporary_predicates[output.name] = [
                operator.gt(
                    CR.conditional_operands[parameters[0].name][0],  # type: ignore
                    CR.conditional_operands[parameters[0].name][1],  # type: ignore
                )
            ]
        elif (
            CR.temporary_predicates[parameters[0].name]
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CR.temporary_predicates[output.name] = CR.temporary_predicates[
                parameters[0].name
            ]
        else:
            CR.temporary_predicates[output.name] = []
        op = operator.gt if output.value[0].lower() == "true" else operator.le
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                op(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name],  # type: ignore
                    z3.IntVal(0),
                ),
            )
        )
    return output


def applyHASH_KEY(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  HASH_KEY  ::  key  :  A  ⇒  key_hash  :  A
    # TODO: should be considered within PCTs but don't know how to model it yet
    return Data(
        "key_hash",
        [b58encode_check(bytes.fromhex(parameters[0].value[0])).decode("utf-8")],
    )


def applyIF(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  instr1  ::  A  ⇒  B
    # Γ  ⊢  instr2  ::  A  ⇒  B
    # Γ  ⊢  IF  instr1  instr2  ::  bool  :  A  ⇒  B
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    local_ephemeral_predicates = []
    # Branch selection
    branch = 0 if parameters[0].value[0].lower() == "true" else 1
    # We now have a single input parameter: parameters[0], a bool. For what we know,
    # it's supposed to be connected to some older predicates we've been
    # collecting in current run's `temporary_predicates`. There could
    # also be a number of predicates within `ephemeral_predicates`
    # which are bound to parameters[0].
    if parameters[0].name in CPC.input_variables | CR.ephemeral_symbolic_variables:
        temp_set = set()
        if (
            CR.temporary_predicates.get(parameters[0].name)
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CPC.predicates.extend(CR.temporary_predicates[parameters[0].name])
            var_set = set()
            for i in CR.temporary_predicates[parameters[0].name]:
                q = deque(i.children())
                while len(q) != 0:
                    te = q.popleft()
                    if hasattr(te, "children") and len(te.children()) != 0:
                        q.extend(te.children())
                    # Taken from: https://stackoverflow.com/a/12324518
                    if z3.is_const(te) and te.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                        var_set.add(te)
            for i in CR.ephemeral_predicates:
                e = set()
                q = deque(i.children())
                while len(q) != 0:
                    te = q.popleft()
                    if hasattr(te, "children") and len(te.children()) != 0:
                        q.extend(te.children())
                    if z3.is_const(te) and te.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                        e.add(te)
                if var_set & e:
                    temp_set.add(i)
            if temp_set:
                local_ephemeral_predicates.extend(temp_set)
                CR.ephemeral_predicates = list(set(CR.ephemeral_predicates) - temp_set)
        else:
            for i in CR.ephemeral_predicates:
                e = set()
                q = deque(i.children())
                while len(q) != 0:
                    te = q.popleft()
                    if hasattr(te, "children") and len(te.children()) != 0:
                        q.extend(te.children())
                    if z3.is_const(te) and te.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                        e.add(te)
                if CR.ephemeral_symbolic_variables[parameters[0].name] in e:
                    temp_set.add(i)
            if temp_set:
                local_ephemeral_predicates.extend(temp_set)
                CR.ephemeral_predicates = list(set(CR.ephemeral_predicates) - temp_set)
        CR.path_constraints.append(deepcopy(CPC))
        if branch == 0:
            CR.path_constraints[-1].predicates.append(
                z3.Not(CR.path_constraints[-1].predicates.pop())
            )
        else:
            CPC.predicates.append(z3.Not(CPC.predicates.pop()))
        # Adding all ephemeral predicates and repeating fork & negate
        for i in local_ephemeral_predicates:
            CPC.predicates.append(i)
            CR.path_constraints.append(deepcopy(CPC))
            CR.path_constraints[-1].predicates.append(
                z3.Not(CR.path_constraints[-1].predicates.pop())
            )
    for i in flatten(instruction["args"][branch]):
        step = process_instruction(i, stack)
        if "IF" not in i["prim"]:
            _variables.CURRENT_RUN.steps.append(step)
    return None


def applyIF_CONS(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  instr1  ::  ty  :  list   ty  :  A  ⇒  B
    # Γ  ⊢  instr2  ::  A  ⇒  B
    # Γ  ⊢  IF_CONS  instr1  instr2  ::  list  ty  :  A  ⇒  B
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    if len(parameters[0].value[0]) > 0:
        d = parameters[0].value[0].pop(0)
        stack.append(parameters[0])
        stack.append(d)
        branch = 0
    else:
        branch = 1

    if parameters[0].name in CPC.input_variables:
        CR.path_constraints.append(deepcopy(CPC))
        CPC.predicates.append(
            operator.gt(CR.symbolic_variables[parameters[0].name], 0)  # type: ignore
            if branch == 0
            else operator.eq(CR.symbolic_variables[parameters[0].name], 0)
        )
        CR.path_constraints[-1].predicates.append(
            operator.eq(CR.symbolic_variables[parameters[0].name], 0)
            if branch == 0
            else operator.gt(CR.symbolic_variables[parameters[0].name], 0)  # type: ignore
        )

    for i in flatten(instruction["args"][branch]):
        step = process_instruction(i, stack)
        if "IF" not in i["prim"]:
            CR.steps.append(step)
    return None


def applyIF_LEFT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  instr1  ::  ty1  :  A  ⇒  B
    # Γ  ⊢  instr2  ::  ty2  :  A  ⇒  B
    # Γ  ⊢  IF_LEFT   instr1   instr2  ::  or   ty1   ty2  :  A  ⇒  B
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    branch = 0 if parameters[0].or_value == "Left" else 1

    if parameters[0].name in CPC.input_variables:
        CR.path_constraints.append(deepcopy(CPC))
        CPC.predicates.append(
            CR.symbolic_variables[parameters[0].name]
            if branch == 0
            else z3.Not(CR.symbolic_variables[parameters[0].name])
        )
        CR.path_constraints[-1].predicates.append(
            z3.Not(CR.symbolic_variables[parameters[0].name])
            if branch == 0
            else CR.symbolic_variables[parameters[0].name]
        )

    stack.append(parameters[0].value[0])
    for i in flatten(instruction["args"][branch]):
        step = process_instruction(i, stack)
        if "IF" not in i["prim"]:
            CR.steps.append(step)
    return None


def applyIF_NONE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # Γ  ⊢  instr1  ::  A  ⇒  B
    # Γ  ⊢  instr2  ::  ty1  :  A  ⇒  B
    # Γ  ⊢  IF_NONE   instr1   instr2  ::  option   ty1  :  A  ⇒  B
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    if parameters[0].option_value == "None":
        branch = 0
    else:
        branch = 1
        stack.append(parameters[0].value[0])

    nested_parameters = find_nested(parameters[0])

    t = [
        parameters[0].name in CPC.input_variables,
        parameters[0].name in CR.ephemeral_symbolic_variables,
        True
        if {i.name for i in nested_parameters}
        & (
            set(CPC.input_variables.keys())
            | set(CR.ephemeral_symbolic_variables.keys())
        )
        else False,
    ]

    if any(t):
        local_ephemeral_predicates = []
        if t[0]:
            CR.path_constraints.append(deepcopy(CPC))
            CPC.predicates.append(
                z3.Not(CR.symbolic_variables[parameters[0].name])
                if branch == 0
                else CR.symbolic_variables[parameters[0].name]
            )
            CR.path_constraints[-1].predicates.append(
                CR.symbolic_variables[parameters[0].name]
                if branch == 0
                else z3.Not(CR.symbolic_variables[parameters[0].name])
            )
        elif t[1]:
            add = set()
            for i in CR.ephemeral_predicates:
                e = set()
                q = deque(i.children())
                while len(q) != 0:
                    te = q.popleft()
                    if hasattr(te, "children") and len(te.children()) != 0:
                        q.extend(te.children())
                    if z3.is_const(te) and te.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                        e.add(te)
                if CR.ephemeral_symbolic_variables[parameters[0].name] in e or {
                    j.name for j in nested_parameters
                } & {str(j) for j in e}:
                    add.add(i)
            if add:
                local_ephemeral_predicates.extend(add)
                CR.ephemeral_predicates = list(set(CR.ephemeral_predicates) - add)
        else:
            for i in nested_parameters:
                if not {i.name} & (
                    set(CPC.input_variables.keys())
                    | set(CR.ephemeral_symbolic_variables.keys())
                ):
                    continue
                temp_set = set()
                if (
                    CR.temporary_predicates.get(i.name)
                    and len(CR.temporary_predicates[i.name]) != 0
                ):
                    CPC.predicates.extend(CR.temporary_predicates[i.name])
                    var_set = set()
                    for j in CR.temporary_predicates[i.name]:
                        q = deque(j.children())
                        while len(q) != 0:
                            te = q.popleft()
                            if hasattr(te, "children") and len(te.children()) != 0:
                                q.extend(te.children())
                            # Taken from: https://stackoverflow.com/a/12324518
                            if (
                                z3.is_const(te)
                                and te.decl().kind() == z3.Z3_OP_UNINTERPRETED
                            ):
                                var_set.add(te)
                    for j in CR.ephemeral_predicates:
                        e = set()
                        q = deque(j.children())
                        while len(q) != 0:
                            te = q.popleft()
                            if hasattr(te, "children") and len(te.children()) != 0:
                                q.extend(te.children())
                            if (
                                z3.is_const(te)
                                and te.decl().kind() == z3.Z3_OP_UNINTERPRETED
                            ):
                                e.add(te)
                        if var_set & e:
                            temp_set.add(j)
                    if temp_set:
                        local_ephemeral_predicates.extend(temp_set)
                        CR.ephemeral_predicates = list(
                            set(CR.ephemeral_predicates) - temp_set
                        )
                else:
                    for j in CR.ephemeral_predicates:
                        e = set()
                        q = deque(j.children())
                        while len(q) != 0:
                            te = q.popleft()
                            if hasattr(te, "children") and len(te.children()) != 0:
                                q.extend(te.children())
                            if (
                                z3.is_const(te)
                                and te.decl().kind() == z3.Z3_OP_UNINTERPRETED
                            ):
                                e.add(te)
                        if (
                            i.name in CPC.input_variables
                            or i.name in CR.ephemeral_symbolic_variables
                        ) in e:
                            temp_set.add(j)
                    if temp_set:
                        local_ephemeral_predicates.extend(temp_set)
                        CR.ephemeral_predicates = list(
                            set(CR.ephemeral_predicates) - temp_set
                        )
        # Adding all ephemeral predicates and repeating fork & negate
        for i in local_ephemeral_predicates:
            CPC.predicates.append(i)
            CR.path_constraints.append(deepcopy(CPC))
            CR.path_constraints[-1].predicates.append(
                z3.Not(CR.path_constraints[-1].predicates.pop())
            )

    for i in flatten(instruction["args"][branch]):
        step = process_instruction(i, stack)
        if "IF" not in i["prim"]:
            CR.steps.append(step)
    return None


def applyIMPLICIT_ACCOUNT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  IMPLICIT_ACCOUNT  ::  key_hash  :  A  ⇒  contract   unit  :  A
    output = Data("contract", [parameters[0]])
    output.contract_type = "unit"
    return output


def applyINT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  INT  ::  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  INT  ::  bls12_381_fr   :  A  ⇒  int  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    output = Data("int", [parameters[0].value[0]])

    if parameters[0].name in CPC.input_variables:
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                CPC.input_variables[parameters[0].name],
            )
        )

    return output


def applyISNAT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  ISNAT  ::  int  :  A  ⇒  option   nat  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    output = Data("option")
    output.option_type.append("nat")
    if int(parameters[0].value[0]) < 0:
        output.option_value = "None"
        if parameters[0].name in CPC.input_variables | CR.ephemeral_symbolic_variables:
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[output.name],
                    (
                        operator.eq(
                            CPC.input_variables[parameters[0].name], z3.IntVal(0)
                        )
                    ),
                )
            )
    else:
        output.option_value = "Some"
        i = Data("nat", [parameters[0].value[0]], output.name)
        if parameters[0].name in CPC.input_variables:
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.ephemeral_symbolic_variables[i.name] = create_symbolic_variable(i)
            CR.ephemeral_predicates.extend(
                [
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name],
                        (
                            operator.ne(
                                CPC.input_variables[parameters[0].name], z3.IntVal(0)
                            )
                        ),
                    ),
                    operator.eq(
                        CR.ephemeral_symbolic_variables[i.name],
                        CPC.input_variables[parameters[0].name],
                    ),
                ]
            )
        output.value.append(i)
    return output


def applyITER(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> None:
    # Γ  ⊢  instr  ::  ty  :  A  ⇒  A
    # Γ  ⊢  ITER   instr  ::  list   ty  :  A  ⇒  A
    # Γ  ⊢  instr  ::  cty  :  A  ⇒  A
    # Γ  ⊢  ITER   instr  ::  set   cty  :  A  ⇒  A
    # Γ  ⊢  instr  ::  (  pair   kty   vty  )  :  A  ⇒  A
    # Γ  ⊢  ITER   instr  ::  map   kty   vty  :  A  ⇒  A
    # Not implemented
    return None


def applyLAMBDA(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> None:
    # None  ⊢  instr  ::  ty1  :   [ ]   ⇒  ty2  :   [ ]
    # Γ  ⊢  LAMBDA   ty1   ty2   instr  ::  A  ⇒  lambda   ty1   ty2  :  A
    # Not implemented
    return None


def applyLE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  LE  ::  int  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("bool")
    if int(parameters[0].value[0]) <= 0:
        output.value.append("True")
    else:
        output.value.append("False")
    if (
        parameters[0].name in CPC.input_variables
        or parameters[0].name in CR.ephemeral_symbolic_variables
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if CR.conditional_operands.get(parameters[0].name):
            CR.temporary_predicates[output.name] = [
                operator.le(
                    CR.conditional_operands[parameters[0].name][0],  # type: ignore
                    CR.conditional_operands[parameters[0].name][1],  # type: ignore
                )
            ]
        elif (
            CR.temporary_predicates[parameters[0].name]
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CR.temporary_predicates[output.name] = CR.temporary_predicates[
                parameters[0].name
            ]
        else:
            CR.temporary_predicates[output.name] = []
        op = operator.le if output.value[0].lower() == "true" else operator.gt
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                op(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name],  # type: ignore
                    z3.IntVal(0),
                ),
            )
        )
    return output


def applyLEFT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  LEFT   ty2  ::  ty1  :  A  ⇒  or   ty1   ty2  :  A
    output = Data("or", [parameters[0]])
    output.or_value = "Left"
    output.or_type.extend([parameters[0].prim, instruction["args"][0].get("prim")])
    return output


def applyLOOP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> None:
    # TODO: PCT
    # Γ  ⊢  instr  ::  A  ⇒  bool  :  A
    # Γ  ⊢  LOOP   instr  ::  bool  :  A  ⇒  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    v = False

    top = stack.pop()
    if top.prim != "bool":
        raise CustomException(
            "top element of stack is not bool",
            {"instruction": instruction, "parameters": parameters},
        )
    else:
        v = top.value[0].lower() == "true"

    t = [
        top.name in CPC.input_variables,
        top.name in CR.ephemeral_symbolic_variables,
    ]

    # PCT
    if any(t):
        if t[0]:
            if v:
                CPC.predicates.append(CR.symbolic_variables[top.name])
            else:
                CPC.predicates.append(z3.Not(CR.symbolic_variables[top.name]))
            CR.path_constraints.append(deepcopy(CPC))
            CR.path_constraints[-1].predicates.append(
                z3.Not(CR.path_constraints[-1].predicates.pop())
            )
        else:
            add = set()
            for i in CR.ephemeral_predicates:
                e = set()
                q = deque(i.children())
                while len(q) != 0:
                    te = q.popleft()
                    if hasattr(te, "children") and len(te.children()) != 0:
                        q.extend(te.children())
                    if z3.is_const(te) and te.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                        e.add(te)
                if CR.ephemeral_symbolic_variables[top.name] in e:
                    add.add(i)
            CPC.predicates.extend(add)
            CR.ephemeral_predicates = list(set(CR.ephemeral_predicates) - add)

    while v:
        for i in flatten(instruction["args"]):
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                CR.steps.append(step)
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
    # Γ  ⊢  instr  ::  ty1  :  A  ⇒  or   ty1   ty2  :  A
    # Γ  ⊢  LOOP_LEFT   instr  ::  or   ty1   ty2  :  A  ⇒  ty2  :  A
    # TODO: PCT
    CR = _variables.CURRENT_RUN
    CPC = _variables.CURRENT_RUN.current_path_constraint
    v = False

    top = stack.pop()
    stack.append(top.value[0])
    if top.prim != "or":
        raise CustomException(
            "top element of stack is not or",
            {"instruction": instruction, "parameters": parameters},
        )
    if top.or_value == "Left":
        v = True

    # PCT
    if top.name in CPC.input_variables:
        if v:
            CPC.predicates.append(CR.symbolic_variables[top.name])
        else:
            CPC.predicates.append(z3.Not(CR.symbolic_variables[top.name]))
        CR.path_constraints.append(deepcopy(CPC))
        CR.path_constraints[-1].predicates.append(
            z3.Not(CR.path_constraints[-1].predicates.pop())
        )
    while v:
        for i in flatten(instruction["args"]):
            step = process_instruction(i, stack)
            if "IF" not in i["prim"]:
                CR.steps.append(step)
        top = stack.pop()
        stack.append(top.value[0])
        v = False
        if top.prim != "or":
            raise CustomException(
                "top element of stack is not or",
                {"instruction": instruction, "parameters": parameters},
            )
        elif top.or_value == "Right":
            return None
        else:
            v = True
    return None


def applyLSL(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  LSL  ::  nat  :  nat  :  A  ⇒  nat  :  A
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
    # Γ  ⊢  LSR  ::  nat  :  nat  :  A  ⇒  nat  :  A
    # TODO: PCT but don't know if logical shifts can be expressed in z3
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
    # Γ  ⊢  LT  ::  int  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("bool")
    if int(parameters[0].value[0]) < 0:
        output.value.append("True")
    else:
        output.value.append("False")
    if (
        parameters[0].name in CPC.input_variables
        or parameters[0].name in CR.ephemeral_symbolic_variables
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if CR.conditional_operands.get(parameters[0].name):
            CR.temporary_predicates[output.name] = [
                operator.lt(
                    CR.conditional_operands[parameters[0].name][0],  # type: ignore
                    CR.conditional_operands[parameters[0].name][1],  # type: ignore
                )
            ]
        elif (
            CR.temporary_predicates[parameters[0].name]
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CR.temporary_predicates[output.name] = CR.temporary_predicates[
                parameters[0].name
            ]
        else:
            CR.temporary_predicates[output.name] = []
        op = operator.lt if output.value[0].lower() == "true" else operator.ge
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                op(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name],  # type: ignore
                    z3.IntVal(0),
                ),
            )
        )
    return output


def applyMAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  instr  ::  ty  :  A  ⇒  ty2  :  A
    # Γ  ⊢  MAP   instr  ::  list   ty  :  A  ⇒  list   ty2  :  A
    # Γ  ⊢  instr  ::  (  pair   kty   ty1  )  :  A  ⇒  ty2  :  A
    # Γ  ⊢  MAP   instr  ::  map   kty   ty1  :  A  ⇒  map   kty   ty2  :  A
    new_list = []
    for _ in range(len(parameters[0].value[0])):
        stack.append(parameters[0].value[0].pop(0))
        for j in flatten(instruction["args"][::-1]):
            step = process_instruction(j, stack)
            if "IF" not in j.prim:
                _variables.CURRENT_RUN.steps.append(step)
        new_list.append(stack.pop())
    parameters[0].value[0] = new_list
    return parameters[0]


def applyMEM(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  MEM  ::  cty  :  set   cty  :  A  ⇒  bool  :  A
    # Γ  ⊢  MEM  ::  kty  :  map   kty   vty  :  A  ⇒  bool  :  A
    # Γ  ⊢  MEM  ::  kty  :  big_map   kty   vty  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    if (
        parameters[1].prim in ["big_map", "map"]
        and parameters[1].key_type != parameters[0].prim
    ) or parameters[1].set_type != parameters[0].prim:
        raise CustomException(
            "key or element type does not match",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data(
        "bool",
        ["True" if parameters[0].value[0] in parameters[1].value[0] else "False"],
    )
    if (
        set(CPC.input_variables.keys()) | set(CR.ephemeral_symbolic_variables.keys())
    ) & set([i.name for i in parameters]):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.temporary_predicates[output.name] = []
        if CR.temporary_predicates[parameters[0].name]:
            CR.temporary_predicates[output.name].extend(
                CR.temporary_predicates[parameters[0].name]
            )
        if CR.temporary_predicates[parameters[1].name]:
            CR.temporary_predicates[output.name].extend(
                CR.temporary_predicates[parameters[1].name]
            )
    return output


def applyMUL(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  MUL  ::  nat  :  nat  :  A  ⇒  nat  :  A
    # Γ  ⊢  MUL  ::  nat  :  int  :  A  ⇒  int  :  A
    # Γ  ⊢  MUL  ::  int  :  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  MUL  ::  int  :  int  :  A  ⇒  int  :  A
    # Γ  ⊢  MUL  ::  mutez  :  nat  :  A  ⇒  mutez  :  A
    # Γ  ⊢  MUL  ::  nat  :  mutez  :  A  ⇒  mutez  :  A
    # Γ  ⊢  MUL  ::  bls12_381_g1  :  bls12_381_fr  :  A  ⇒  bls12_381_g1  :  A
    # Γ  ⊢  MUL  ::  bls12_381_g2  :  bls12_381_fr  :  A  ⇒  bls12_381_g2  :  A
    # Γ  ⊢  MUL  ::  bls12_381_fr  :  bls12_381_fr  :  A  ⇒  bls12_381_fr  :  A
    # Γ  ⊢  MUL  ::  nat  :  bls12_381_fr   :  A  ⇒  bls12_381_fr  :  A
    # Γ  ⊢  MUL  ::  int  :  bls12_381_fr   :  A  ⇒  bls12_381_fr  :  A
    # Γ  ⊢  MUL  ::  bls12_381_fr  :  nat  :  A  ⇒  bls12_381_fr  :  A
    # Γ  ⊢  MUL  ::  bls12_381_fr  :  int  :  A  ⇒  bls12_381_fr  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

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
    output = Data(t, [str(z1 * z2)])
    if set(CPC.input_variables.keys()) & set([i.name for i in parameters]):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                operator.mul(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else z3.IntVal(z1),
                    CPC.input_variables[parameters[1].name]
                    if parameters[1].name in CPC.input_variables
                    else z3.IntVal(z2),
                ),
            )
        )
    return output


def applyNEG(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  NEG  ::  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  NEG  ::  int  :  A  ⇒  int  :  A
    # Γ  ⊢  NEG  ::  bls12_381_g1  :  A  ⇒  bls12_381_g1  :  A
    # Γ  ⊢  NEG  ::  bls12_381_g2  :  A  ⇒  bls12_381_g2  :  A
    # Γ  ⊢  NEG  ::  bls12_381_fr  :  A  ⇒  bls12_381_fr  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    output = Data("int", [str(-int(parameters[0].value[0]))])

    if parameters[0].name in CPC.input_variables:
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                operator.neg(CPC.input_variables[parameters[0].name]),  # type: ignore
            )
        )

    return output


def applyNEQ(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  NEQ  ::  int  :  A  ⇒  bool  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint
    output = Data("bool")
    if int(parameters[0].value[0]) != 0:
        output.value.append("True")
    else:
        output.value.append("False")
    if (
        parameters[0].name in CPC.input_variables
        or parameters[0].name in CR.ephemeral_symbolic_variables
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if CR.conditional_operands.get(parameters[0].name):
            CR.temporary_predicates[output.name] = [
                operator.ne(
                    CR.conditional_operands[parameters[0].name][0],
                    CR.conditional_operands[parameters[0].name][1],
                )
            ]
        elif (
            CR.temporary_predicates[parameters[0].name]
            and len(CR.temporary_predicates[parameters[0].name]) != 0
        ):
            CR.temporary_predicates[output.name] = CR.temporary_predicates[
                parameters[0].name
            ]
        else:
            CR.temporary_predicates[output.name] = []
        op = operator.ne if output.value[0].lower() == "true" else operator.eq
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                op(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else CR.ephemeral_symbolic_variables[parameters[0].name],
                    z3.IntVal(0),
                ),  # type: ignore
            )
        )
    return output


def applyNIL(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  NIL   ty  ::  A  ⇒  list   ty  :  A
    if "args" not in instruction:
        raise CustomException(
            "type of list is not declared",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("list", [[]])
    output.list_type = instruction["args"][0].get("prim")
    return output


def applyNONE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  NONE   ty  ::  A  ⇒  option   ty  :  A
    if "args" not in instruction:
        raise CustomException(
            "type of option is not declared",
            {"instruction": instruction, "parameters": parameters},
        )
    output = Data("option", [instruction["args"][0].get("prim")])
    output.option_value = "None"
    output.option_type.extend([x.get("prim") for x in instruction["args"]])
    return output


def applyNOT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  NOT  ::  bool  :  A  ⇒  bool  :  A
    # Γ  ⊢  NOT  ::  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  NOT  ::  int  :  A  ⇒  int  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    match parameters[0].prim:
        case "int" | "nat":
            return Data("int", [str(~int(parameters[0].value[0]))])
        case "bool":
            output = Data("bool", [str(parameters[0].value[0].lower() == "true")])
            if (
                parameters[0].name in CPC.input_variables
                or parameters[0].name in CR.ephemeral_symbolic_variables
            ):
                CR.ephemeral_concrete_variables[output.name] = output
                CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                    output
                )
                if (
                    CR.temporary_predicates[parameters[0].name]
                    and len(CR.temporary_predicates[parameters[0].name]) != 0
                ):
                    CR.temporary_predicates[output.name] = CR.temporary_predicates[
                        parameters[0].name
                    ]
                else:
                    CR.temporary_predicates[output.name] = []
                CR.ephemeral_predicates.append(
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name],
                        operator.neg(
                            CPC.input_variables[parameters[0].name]
                            if parameters[0].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[0].name]  # type: ignore
                        ),
                    )
                )
            return output
        case _:
            raise CustomException(
                "unknown prim", {"instruction": instruction, "parameters": parameters}
            )


def applyNOW(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  NOW  ::  A  ⇒  timestamp  :  A
    return Data(
        "timestamp",
        [str(_variables.CURRENT_RUN.current_state.timestamp)],
        None,
        "sv_now",
    )


def applyOR(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  OR  ::  bool  :  bool  :  A  ⇒  bool  :  A
    # Γ  ⊢  OR  ::  nat  :  nat  :  A  ⇒  nat  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    if parameters[0].prim == "bool":
        output = Data(
            "bool",
            [
                str(
                    (parameters[0].value[0].lower()) == "true"
                    or (parameters[1].value[0].lower() == "true")
                )
            ],
        )
        if (
            set(CPC.input_variables.keys())
            | set(CR.ephemeral_symbolic_variables.keys())
        ) & set([i.name for i in parameters]):
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.temporary_predicates[output.name] = []
            if CR.temporary_predicates[parameters[0].name]:
                CR.temporary_predicates[output.name].extend(
                    CR.temporary_predicates[parameters[0].name]
                )
            if CR.temporary_predicates[parameters[1].name]:
                CR.temporary_predicates[output.name].extend(
                    CR.temporary_predicates[parameters[1].name]
                )
            op1 = (
                CPC.input_variables[parameters[0].name]
                if parameters[0].name in CPC.input_variables
                else CR.ephemeral_symbolic_variables[parameters[0].name]
                if parameters[0].name in CR.ephemeral_symbolic_variables
                else z3.BoolVal(parameters[0].value[0].lower() == "true")
            )
            op2 = (
                CPC.input_variables[parameters[1].name]
                if parameters[1].name in CPC.input_variables
                else CR.ephemeral_symbolic_variables[parameters[1].name]
                if parameters[1].name in CR.ephemeral_symbolic_variables
                else z3.BoolVal(parameters[1].value[0].lower() == "true")
            )
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[output.name], z3.Or(op1, op2)
                )
            )
        return output
    else:
        return Data(
            "nat", [str(int(parameters[0].value[0]) | int(parameters[1].value[0]))]
        )


def applyPACK(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  PACK  ::  ty  :  A  ⇒  bytes  :  A
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
    # Γ  ⊢  PAIR  ::  ty1  :  ty2  :  A  ⇒  pair   ty1   ty2  :  A
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
    # Γ  ⊢  x  ::  ty
    # Γ  ⊢  PUSH   ty   x  ::  A  ⇒  ty  :  A
    dk = {"int", "string", "bytes", "prim"}
    output = Data(instruction["args"][0]["prim"])
    match instruction["args"][0]["prim"]:
        case "list":
            output.value.append([])
            output.list_type = instruction["args"][0]["args"][0].get("prim")
            for i in range(1, len(instruction["args"])):
                output.value[0].append(
                    Data(
                        output.list_type,
                        [
                            instruction["args"][i].get(
                                list(set(instruction["args"][i].keys()) & dk)[0]
                            )
                        ],
                        output.name,
                    )
                )
        case "option":
            output.option_value = instruction["args"][1].get("prim")
            output.option_type.append(instruction["args"][0]["args"][0].get("prim"))
            if output.option_value != "None":
                output.value.append(
                    Data(
                        output.option_type[0],
                        [
                            instruction["args"][1]["args"][0].get(
                                list(
                                    set(instruction["args"][1]["args"][0].keys()) & dk
                                )[0]
                            )
                        ],
                        output.name,
                    )
                )
        case "or":
            output.or_value = instruction["args"][1].get("prim")
            output.or_type = [x.get("prim") for x in instruction["args"][0].get("args")]
            output.value.append(
                Data(
                    output.or_type[0]
                    if output.or_value == "Left"
                    else output.or_type[1],
                    [
                        instruction["args"][1]["args"][0].get(
                            list(set(instruction["args"][1]["args"][0].keys()) & dk)[0]
                        )
                    ],
                    output.name,
                )
            )
        case _:
            output.value.append(
                [
                    instruction["args"][1].get(
                        list(set(instruction["args"][1].keys()) & dk)[0]
                    )
                ][0]
            )
    return output


def applyRIGHT(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  RIGHT   ty1  ::  ty2  :  A  ⇒  or   ty1   ty2  :  A
    output = Data("or", [parameters[0]])
    parameters[0].parent = output.name
    output.or_value = "Right"
    output.or_type.extend([instruction["args"][0].get("prim"), parameters[0].prim])
    return output


def applySELF(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  =  Some   ty
    # Γ  ⊢  SELF  ::  A  ⇒  contract   ty  :  A
    # Not implemented completely
    output = Data("contract", [], None, "sv_self")
    output.contract_type = "unit"
    output.value.append(
        Data("address", [_variables.CURRENT_RUN.current_state.address], output.name)
    )
    return output


def applySENDER(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  SENDER  ::  A  ⇒  address  :  A
    # Not implemented completely/correctly
    return Data(
        "address", [_variables.CURRENT_RUN.current_state.address], None, "sv_sender"
    )


def applySET_DELEGATE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  SET_DELEGATE  ::  option   key_hash  :  A  ⇒  operation  :  A
    # Not implemented
    return Data("operation")


def applySHA256(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢   SHA256   ::  bytes  :  A  ⇒  bytes  :  A
    return Data("bytes", [sha256(bytes(parameters[0].value[0])).hexdigest()])


def applySHA512(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢   SHA512   ::  bytes  :  A  ⇒  bytes  :  A
    return Data("bytes", [sha512(bytes(parameters[0].value[0])).hexdigest()])


def applySIZE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  SIZE  ::  set   cty  :  A  ⇒  nat  :  A
    # Γ  ⊢  SIZE  ::  map   kty   vty  :  A  ⇒  nat  :  A
    # Γ  ⊢  SIZE  ::  list   ty  :  A  ⇒  nat  :  A
    # Γ  ⊢  SIZE  ::  string  :  A  ⇒  nat  :  A
    # Γ  ⊢  SIZE  ::  bytes  :  A  ⇒  nat  :  A
    return Data("nat", [str(len(parameters[0].value[0]))])


def applySLICE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  SLICE  ::  nat  :  nat  :  string  :  A  ⇒  option   string  :  A
    # Γ  ⊢  SLICE  ::  nat  :  nat  :  bytes  :  A  ⇒  option   bytes  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    _offset = int(parameters[0].value[0])
    _len = int(parameters[1].value[0])
    _str = parameters[2].value[0]
    output = Data("option")
    output.option_type.append(parameters[2].prim)
    if len(_str) == 0 or _offset >= len(_str) or _offset + _len > len(_str):
        output.option_value = "None"
    elif _offset < len(_str) and _offset + _len <= len(_str):
        output.option_value = "Some"
        output.value.append(
            Data(
                parameters[2].prim, [_str[slice(_offset, _offset + _len)]], output.name
            )
        )
    # TODO: confusing and inefficient
    if set(i.name for i in parameters) & (
        set(CPC.input_variables.keys()) | set(CR.ephemeral_symbolic_variables.keys())
    ):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        if output.option_value == "None":
            if len(_str) == 0 and parameters[2].name in (
                set(CPC.input_variables.keys())
                | set(CR.ephemeral_symbolic_variables.keys())
            ):
                CR.ephemeral_predicates.append(
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name],
                        operator.eq(
                            z3.Length(
                                CPC.input_variables[parameters[2].name]
                                if parameters[2].name in CPC.input_variables
                                else CR.ephemeral_symbolic_variables[parameters[2].name]
                            ),
                            z3.IntVal(0),
                        ),
                    )
                )
            elif _offset >= len(_str) and {parameters[0].name, parameters[2].name} & (
                set(CPC.input_variables.keys())
                | set(CR.ephemeral_symbolic_variables.keys())
            ):
                CR.ephemeral_predicates.append(
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name],
                        operator.ge(
                            CPC.input_variables[parameters[0].name]
                            if parameters[0].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[0].name]
                            if parameters[0].name in CR.ephemeral_symbolic_variables
                            else z3.IntVal(parameters[0].value[0]),  # type: ignore
                            z3.Length(
                                CPC.input_variables[parameters[2].name]
                                if parameters[2].name in CPC.input_variables
                                else CR.ephemeral_symbolic_variables[parameters[2].name]
                                if parameters[2].name in CR.ephemeral_symbolic_variables
                                else parameters[2].value[0],  # type: ignore
                            ),
                        ),
                    )
                )
            else:
                CR.ephemeral_predicates.append(
                    operator.eq(
                        CR.ephemeral_symbolic_variables[output.name],
                        operator.gt(
                            CPC.input_variables[parameters[0].name]
                            if parameters[0].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[0].name]
                            if parameters[0].name in CR.ephemeral_symbolic_variables
                            else z3.IntVal(parameters[0].value[0])
                            + CPC.input_variables[parameters[1].name]
                            if parameters[1].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[1].name]
                            if parameters[1].name in CR.ephemeral_symbolic_variables
                            else z3.IntVal(parameters[1].value[0]),  # type: ignore
                            z3.Length(
                                CPC.input_variables[parameters[2].name]
                                if parameters[2].name in CPC.input_variables
                                else CR.ephemeral_symbolic_variables[parameters[2].name]
                                if parameters[2].name in CR.ephemeral_symbolic_variables
                                else parameters[2].value[0],  # type: ignore
                            ),
                        ),
                    )
                )
        else:
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[output.name],
                    z3.And(
                        operator.lt(
                            CPC.input_variables[parameters[0].name]
                            if parameters[0].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[0].name]
                            if parameters[0].name in CR.ephemeral_symbolic_variables
                            else z3.IntVal(parameters[0].value[0]),  # type: ignore
                            z3.Length(
                                CPC.input_variables[parameters[2].name]
                                if parameters[2].name in CPC.input_variables
                                else CR.ephemeral_symbolic_variables[parameters[2].name]
                                if parameters[2].name in CR.ephemeral_symbolic_variables
                                else parameters[2].value[0],
                            ),
                        ),
                        operator.le(
                            CPC.input_variables[parameters[0].name]
                            if parameters[0].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[0].name]
                            if parameters[0].name in CR.ephemeral_symbolic_variables
                            else z3.IntVal(parameters[0].value[0])
                            + CPC.input_variables[parameters[1].name]
                            if parameters[1].name in CPC.input_variables
                            else CR.ephemeral_symbolic_variables[parameters[1].name]
                            if parameters[1].name in CR.ephemeral_symbolic_variables
                            else z3.IntVal(parameters[1].value[0]),  # type: ignore
                            z3.Length(
                                CPC.input_variables[parameters[2].name]
                                if parameters[2].name in CPC.input_variables
                                else CR.ephemeral_symbolic_variables[parameters[2].name]
                                if parameters[2].name in CR.ephemeral_symbolic_variables
                                else parameters[2].value[0],
                            ),
                        ),
                    ),
                )
            )
    return output


def applySOME(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  SOME  ::  ty1  :  A  ⇒  option   ty1  :  A
    output = Data("option", [parameters[0]])
    parameters[0].parent = output.name
    output.option_value = "Some"
    output.option_type.append(parameters[0].prim)
    return output


def applySOURCE(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  SOURCE  ::  A  ⇒  address  :  A
    # Not implemented completely
    return Data(
        "address", [_variables.CURRENT_RUN.current_state.address], None, "sv_source"
    )


def applySUB(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  SUB  ::  nat  :  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  SUB  ::  nat  :  int  :  A  ⇒  int  :  A
    # Γ  ⊢  SUB  ::  int  :  nat  :  A  ⇒  int  :  A
    # Γ  ⊢  SUB  ::  int  :  int  :  A  ⇒  int  :  A
    # Γ  ⊢  SUB  ::  timestamp  :  int  :  A  ⇒  timestamp  :  A
    # Γ  ⊢  SUB  ::  timestamp  :  timestamp  :  A  ⇒  int  :  A
    # Γ  ⊢  SUB  ::  mutez  :  mutez  :  A  ⇒  mutez  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

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
    prim = ""

    match parameters[0].prim:
        case "nat" | "int":
            prim = "int"
        case "timestamp":
            prim = "timestamp" if parameters[1].prim == "int" else "int"
        case "mutez":
            prim = "mutez"
    output = Data(prim, [str(z1 - z2)])
    if set(CPC.input_variables.keys()) & set([i.name for i in parameters]):
        CR.ephemeral_concrete_variables[output.name] = output
        CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(output)
        CR.ephemeral_predicates.append(
            operator.eq(
                CR.ephemeral_symbolic_variables[output.name],
                operator.sub(
                    CPC.input_variables[parameters[0].name]
                    if parameters[0].name in CPC.input_variables
                    else parameters[0].value[0],
                    CPC.input_variables[parameters[1].name]
                    if parameters[1].name in CPC.input_variables
                    else parameters[1].value[0],
                ),
            )
        )
    return output


def applySWAP(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> List:
    # Γ  ⊢  SWAP  ::  ty1  :  ty2  :  A  ⇒  ty2  :  ty1  :  A
    return list(parameters)[::-1]


def applyTRANSFER_TOKENS(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  TRANSFER_TOKENS  ::  ty  :  mutez  :  contract   ty  :  A  ⇒  operation  :  A
    # Not implemented
    return Data("operation")


def applyUNIT(
    instruction: Dict[str, Any],
    parameters: Deque[Data] | None,
    stack: Deque[Data],
) -> Data:
    # Γ  ⊢  UNIT  ::  A  ⇒  unit  :  A
    return Data("unit", ["Unit"])


def applyUNPACK(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  UNPACK   ty  ::  bytes  :  A  ⇒  option   ty  :  A
    # Type check is not being done here
    v = ast.literal_eval(
        json.dumps(bytes.fromhex(parameters[0].value[0]).decode("utf-8"))
    )
    output = Data("option")
    i = Data(instruction["args"][0]["prim"], [], output.name)
    # TODO: Don't know why this check is here
    if "args" in instruction["args"][0] and all(
        y == v[x].prim
        for x, y in enumerate(map(lambda x: x.prim, instruction["args"][0]["args"]))
    ):
        i.value = v
    else:
        i.value = v
    # Not implemented
    output.option_value = "Some"
    output.option_type.append(instruction["args"][0].get("prim"))
    output.value.append(i)
    return output


def applyUPDATE(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
):
    # Γ  ⊢  UPDATE  ::  cty  :  bool  :  set   cty  :  A  ⇒  set   cty  :  A
    # Γ  ⊢  UPDATE  ::  kty  :  option   vty  :  map   kty   vty  :  A  ⇒  map   kty   vty  :  A
    # Γ  ⊢  UPDATE  ::  kty  :  option   vty  :  big_map   kty   vty  :  A  ⇒  big_map   kty   vty  :  A
    # TODO: missing Data parent update
    if parameters[1].prim == "bool":
        if parameters[0].prim != parameters[2].set_type:
            raise CustomException(
                "set type does not match",
                {"instruction": instruction, "parameters": parameters},
            )
        if parameters[1].value[0].lower() == "true":
            parameters[2].value[0].add(parameters[2].value)
        else:
            parameters[2].value[0].remove(parameters[2].value)
    else:
        if parameters[0].prim != parameters[2].key_type:
            raise CustomException(
                "key type does not match",
                {"instruction": instruction, "parameters": parameters},
            )
        if parameters[1].option_value == "Some":
            if parameters[1].option_type[0] != parameters[2].value_type:
                raise CustomException(
                    "value type does not match",
                    {"instruction": instruction, "parameters": parameters},
                )
            parameters[2].value[0][parameters[0].value[0]] = parameters[1].value[0]
        elif parameters[0].value[0] in parameters[2].value[0]:
            parameters[2].value[0].pop(parameters[0].value[0])
    return parameters[2]


def applyXOR(
    instruction: Dict[str, Any], parameters: Deque[Data], stack: Deque[Data]
) -> Data:
    # Γ  ⊢  XOR  ::  bool  :  bool  :  A  ⇒  bool  :  A
    # Γ  ⊢  XOR  ::  nat  :  nat  :  A  ⇒  nat  :  A
    CR = _variables.CURRENT_RUN
    CPC = CR.current_path_constraint

    if parameters[0].prim == "bool":
        output = Data(
            "bool",
            [str(parameters[0].value[0].lower() != parameters[1].value[0].lower())],
        )
        # For now, only implemented for bool
        if (
            set(CPC.input_variables.keys())
            | set(CR.ephemeral_symbolic_variables.keys())
        ) & set([i.name for i in parameters]):
            CR.ephemeral_concrete_variables[output.name] = output
            CR.ephemeral_symbolic_variables[output.name] = create_symbolic_variable(
                output
            )
            CR.temporary_predicates[output.name] = []
            if CR.temporary_predicates[parameters[0].name]:
                CR.temporary_predicates[output.name].extend(
                    CR.temporary_predicates[parameters[0].name]
                )
            if CR.temporary_predicates[parameters[1].name]:
                CR.temporary_predicates[output.name].extend(
                    CR.temporary_predicates[parameters[1].name]
                )
            op1 = (
                CPC.input_variables[parameters[0].name]
                if parameters[0].name in CPC.input_variables
                else CR.ephemeral_symbolic_variables[parameters[0].name]
                if parameters[0].name in CR.ephemeral_symbolic_variables
                else z3.BoolVal(parameters[0].value[0].lower() == "true")
            )
            op2 = (
                CPC.input_variables[parameters[1].name]
                if parameters[1].name in CPC.input_variables
                else CR.ephemeral_symbolic_variables[parameters[1].name]
                if parameters[1].name in CR.ephemeral_symbolic_variables
                else z3.BoolVal(parameters[1].value[0].lower() == "true")
            )
            CR.ephemeral_predicates.append(
                operator.eq(
                    CR.ephemeral_symbolic_variables[output.name], z3.Xor(op1, op2)
                )
            )
        return output
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
    output.key_type = args[0].get("prim")
    output.value_type = args[1].get("prim")

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
        match output.key_type:
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
        output.value[0][re.sub(r'^"(.+(?="$))"$', r"\1", r[1])] = globals()[
            "parse" + output.value_type.upper()
        ](args[1], r[2])
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
    output.list_type = args[0].get("prim")

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
        v: Data = globals()["parse" + output.list_type.upper()](args[0], i)
        v.parent = output.name
        output.value[0].append(v)
    return output


def parseMAP(args, value) -> Data:
    output = Data("map", [dict()])
    output.key_type = args[0].get("prim")
    output.value_type = args[1].get("prim")

    params = re.match(
        r"\s*\{\s*((?:Elt\s+.+\s+.+\s*;\s*)+(?:Elt\s+.+\s+.+\s*)?)\}\s*", value
    )
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    kv_list = [x.strip() for x in params[1].split(";")]
    if kv_list[len(kv_list) - 1] == "":
        kv_list.pop()
    for i in kv_list:
        kv = re.match(r'Elt\s+([a-zA-Z0-9"_ ]+)\s+(.+)', i)
        if kv is None:
            raise CustomException(
                "input doesn't match with the specified types",
                {"args": args, "value": value},
            )
        # r[1] is the key, and r[2] is the value
        match output.key_type:
            case (
                "int" | "mutez" | "nat" | "timestamp" | "bytes" | "signature" | "bool"
            ):
                if kv[1] in output.value[0]:
                    raise CustomException(
                        "key already present in map", {"args": args, "value": value}
                    )
                else:
                    k = kv[1]
            case ("string" | "address" | "key" | "key_hash"):
                if re.sub(r'^"(.+(?="$))"$', r"\1", kv[1]) in output.value[0]:
                    raise CustomException(
                        "key already present in map", {"args": args, "value": value}
                    )
                else:
                    k = re.sub(r'^"(.+(?="$))"$', r"\1", kv[1])
            case _:
                raise CustomException("not implemented", {"args": args, "value": value})
        output.value[0][k] = globals()["parse" + output.value_type.upper()](
            args[1], kv[2]
        )
    return output


def parseMUTEZ(args, value) -> Data:
    return Data("mutez", [value])


def parseNAT(args, value) -> Data:
    return Data("nat", [value])


def parseOPTION(args, value) -> Data:
    # Currently no parameter type check is being done
    output = Data("option")
    output.option_type.append(args[0].get("prim"))
    params = re.match(r"\s*\(\s*(?:(?:Some)\s+(.+)|(?:None)\s*)\s*\)\s*", value)
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    if "None" in params[0]:
        output.option_value = "None"
    else:
        output.option_value = "Some"
        v: Data = globals()["parse" + output.option_type[0].upper()](args, params[1])
        v.parent = output.name
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
    output.or_value = params[1]
    output.or_type = [x.get("prim") for x in args]
    v = Data(
        output.or_type[0] if output.or_value == "Left" else output.or_type[1],
        [params[2]],
    )
    v.parent = output.name
    output.value.append(v)
    return output


def parsePAIR(args, value) -> Data:
    output = Data("pair")
    params = re.match(
        r"\s*\(\s*Pair\s+((?:\(.+\))|(?:.+?))\s+((?:\(.+\))|(?:.+?))\s*\)\s*", value
    )
    if params is None:
        raise CustomException(
            "input doesn't match with the specified types",
            {"args": args, "value": value},
        )
    v1: Data = globals()["parse" + args[0]["prim"].upper()](
        args[0].get("args", []), params[1]
    )
    v1.parent = output.name
    v2: Data = globals()["parse" + args[1]["prim"].upper()](
        args[1].get("args", []), params[2]
    )
    v2.parent = output.name
    output.value.extend([v1, v2])
    return output


def parseSET(args, value) -> Data:
    output = Data("set", [set()])
    output.set_type = args[0].get("prim")

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
        match output.set_type:
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
    return Data("signature", [re.sub(r'^"(.+(?="$))"$', r"\1", value)])


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


def find_nested(d: Data) -> List[Data]:
    o = []
    for i in d.value:
        if isinstance(i, Data):
            o.extend([i] + find_nested(i))
    return o


def flatten(l: List) -> List:
    o = []
    for i in l:
        if isinstance(i, list):
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
