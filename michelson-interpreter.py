#!/usr/bin/python3
import copy
import io
import json
import re
import subprocess
import sys

import click

from _types import CustomException, Data, Delta, State, Step
from _functions import flatten, initialize, process_instruction
from _variables import CURRENT_STATE, STACK, STATES, STEPS


def excepthook(type: Exception, value: CustomException, traceback):
    global CURRENT_STATE, STACK, STEPS
    print("Got exception, details below:")
    print(value)
    print("-------------------------------")
    print("Content of the exception:")
    print(value.extra_params)
    print("-------------------------------")
    print("State at the time of exception:")
    print(CURRENT_STATE)
    print("-------------------------------")
    print("Stack at the time of exception:")
    print(STACK)
    print("-------------------------------")
    print("Recorded steps at the time of exception:")
    print(STEPS)


sys.excepthook = excepthook


def michelson_interpreter(
    script: io.TextIOWrapper, parameter: str, storage: str, state: State
):
    global CURRENT_STATE
    global STACK
    global STATES
    global STEPS

    CURRENT_STATE = state
    s = subprocess.run(
        ["./ext/michelson-parser-wrapper/bin/michelson-parser.js"],
        capture_output=True,
        encoding="utf-8",
        stdin=script,
    )
    s = json.loads(re.sub(r"\\\\\"", '\\"', s.stdout).strip()[1:-1])
    if len(s) > 1:
        raise Exception("Multiple parsings!")
    s = json.loads(s[0])
    parameter_type, storage_type, code = (
        s[0],
        s[1],
        flatten(flatten(s[2]["args"])),
    )
    STACK.append(
        initialize(
            parameter_type["args"][0], parameter, storage_type["args"][0], storage
        )
    )
    STATES.append(copy.deepcopy(CURRENT_STATE))
    STEPS.append(Step(Delta([], [STACK[0]]), [parameter_type, storage_type], STACK))

    for i in code:
        step = process_instruction(i, STACK)
        if step is not None and "IF" not in i["prim"]:
            STEPS.append(step)

    print(STEPS)


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as f:
        michelson_interpreter(f, sys.argv[2], sys.argv[3], State())
