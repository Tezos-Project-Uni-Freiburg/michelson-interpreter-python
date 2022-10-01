#!/usr/bin/python3
import copy
import dataclasses
import datetime
import json
import re
import subprocess
import sys
from collections import deque

import click
import z3

import _functions
import _types
import _variables
from _functions import (
    initialize,
    process_ifmacro,
    process_instruction,
    process_unpairmacro,
)


def excepthook(type, value, traceback):
    # raise value
    print(
        f"""Got exception, details below:
{value}
-------------------------------
Content of the exception:
{json.dumps(value.extra_params if hasattr(value, "extra_params") else [])}
-------------------------------
State at the time of exception:
{json.dumps(dataclasses.asdict(_variables.CURRENT_STATE))}
-------------------------------
Stack at the time of exception:
{json.dumps([dataclasses.asdict(x) for x in _variables.STACK])}
-------------------------------
Recorded steps at the time of exception:
{json.dumps([dataclasses.asdict(x) for x in _variables.STEPS])}
"""
    )


sys.excepthook = excepthook


@click.command()
@click.option(
    "-p", "--parameter", help="Parameter value for the script", required=True, type=str
)
@click.option(
    "-s", "--storage", help="Storage value for the script", required=True, type=str
)
@click.option(
    "--account", default="", show_default=True, help="Account as a string", type=str
)
@click.option(
    "--address", default="", show_default=True, help="Address as a string", type=str
)
@click.option(
    "--amount", default=0, show_default=True, help="Amount as an int", type=int
)
@click.option(
    "--balance", default=0, show_default=True, help="Balance as an int", type=int
)
@click.option(
    "--entrypoint",
    default="default",
    show_default=True,
    help="Entrypoint as a string",
    type=str,
)
@click.option(
    "--gas_limit", default=0, show_default=True, help="Gas limit as an int", type=int
)
@click.option(
    "--id", "_id", default=0, show_default=True, help="id as an int", type=int
)
@click.option(
    "--timestamp",
    default=int(datetime.datetime.now().timestamp()),
    show_default=True,
    help="Timestamp, an int as an Unix time",
    type=int,
)
@click.argument("script", type=click.Path(exists=True, dir_okay=False, readable=True))
def michelson_interpreter(
    parameter: str,
    storage: str,
    account: str,
    address: str,
    amount: int,
    balance: int,
    entrypoint: str,
    gas_limit: int,
    _id: int,
    timestamp,
    script: click.Path,
):
    _variables.CURRENT_STATE = _types.State(
        account, address, amount, balance, entrypoint, gas_limit, _id, timestamp
    )
    CPC = _variables.CURRENT_PATH_CONSTRAINT = _types.PathConstraint()
    _variables.PATH_CONSTRAINTS.append(_variables.CURRENT_PATH_CONSTRAINT)

    with open(str(script), encoding="utf-8") as f:
        s = subprocess.run(
            ["./ext/michelson-parser-wrapper/bin/michelson-parser.js"],
            capture_output=True,
            encoding="utf-8",
            stdin=f,
        )
    s = json.loads(re.sub(r"\\\\\"", '\\"', s.stdout).strip()[1:-1])
    if len(s) > 1:
        raise Exception("Multiple parsings!")
    s = json.loads(s[0])
    parameter_type, storage_type, code = (
        s[0],
        s[1],
        s[2]["args"],
    )

    _variables.STACK.append(
        initialize(
            parameter_type["args"][0], parameter, storage_type["args"][0], storage
        )
    )
    # Adding the initial `pair` as a bool here
    CPC.input_variables = {
        _variables.STACK[-1].name: _types.SYMBOLIC_VARIABLES.get(
            _variables.STACK[-1].name, z3.Bool(_variables.STACK[-1].name)
        )
    }
    # Adding whatever's inside that `pair` + state variables
    CPC.input_variables.update(
        {
            x: _types.SYMBOLIC_VARIABLES.get(x, z3.Bool(x))
            for x in _functions.find_nested(_variables.STACK[-1])
            + [
                _functions.applyAMOUNT({}, None, deque()).name,
                _functions.applyBALANCE({}, None, deque()).name,
                _functions.applyCHAIN_ID({}, None, deque()).name,
                _functions.applyNOW({}, None, deque()).name,
                _functions.applySELF({}, None, deque()).name,
                _functions.applySENDER({}, None, deque()).name,
                _functions.applySOURCE({}, None, deque()).name,
            ]
        }
    )
    _variables.STATES.append(copy.deepcopy(_variables.CURRENT_STATE))
    _variables.STEPS.append(
        _types.Step(
            _types.Delta([], [_variables.STACK[0]]),
            [parameter_type, storage_type],
            list(copy.deepcopy(_variables.STACK)),
        )
    )

    for i in code:
        if isinstance(i, list):
            if i[-1]["prim"] == "IF":
                process_ifmacro(i)
            else:
                process_unpairmacro(i)
        else:
            step = process_instruction(i, _variables.STACK)
            if step is not None and "IF" not in i["prim"]:
                _variables.STEPS.append(step)

    _variables.CURRENT_PATH_CONSTRAINT.is_processed = (
        _variables.CURRENT_PATH_CONSTRAINT.is_satisfiable
    ) = True

    print(
        json.dumps(
            [dataclasses.asdict(x) for x in _variables.STEPS],
            default=lambda x: list(x) if isinstance(x, set) else x,
        )
    )
    print(
        json.dumps(
            [dataclasses.asdict(x) for x in _variables.PATH_CONSTRAINTS],
            default=lambda x: str(x) if isinstance(x, z3.Z3PPObject) else x,
        )
    )


if __name__ == "__main__":
    michelson_interpreter()
