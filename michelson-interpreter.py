#!/usr/bin/python3
import copy
import dataclasses
import json
import re
import subprocess
import sys
import click

from _types import Delta, State, Step
from _functions import flatten, initialize, process_instruction
import _variables


def excepthook(type, value, traceback):
    # raise value
    print(
        f"""Got exception, details below:
{value}
-------------------------------
Content of the exception:
{json.dumps(value.extra_params)}
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
    default=0,
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
    entrypoint: str,
    gas_limit: int,
    _id: int,
    timestamp,
    script: click.Path,
):
    _variables.CURRENT_STATE = State(
        account, address, amount, entrypoint, gas_limit, _id, timestamp
    )
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
        flatten(flatten(s[2]["args"])),
    )
    _variables.STACK.append(
        initialize(
            parameter_type["args"][0], parameter, storage_type["args"][0], storage
        )
    )
    _variables.STATES.append(copy.deepcopy(_variables.CURRENT_STATE))
    _variables.STEPS.append(
        Step(
            Delta([], [_variables.STACK[0]]),
            [parameter_type, storage_type],
            list(copy.deepcopy(_variables.STACK)),
        )
    )

    for i in code:
        step = process_instruction(i, _variables.STACK)
        if step is not None and "IF" not in i["prim"]:
            _variables.STEPS.append(step)

    print(json.dumps([dataclasses.asdict(x) for x in _variables.STEPS]))


if __name__ == "__main__":
    michelson_interpreter()
