#!/usr/bin/python3
from __future__ import annotations

import copy
import dataclasses
import datetime
import json
import re
import subprocess
import sys
from collections import deque
from typing import Any, Dict

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
{json.dumps(dataclasses.asdict(_variables.CURRENT_RUN.current_state))}
-------------------------------
Stack at the time of exception:
{json.dumps([dataclasses.asdict(x) for x in _variables.CURRENT_RUN.stack])}
-------------------------------
Recorded steps at the time of exception:
{json.dumps([dataclasses.asdict(x) for x in _variables.CURRENT_RUN.steps])}
"""
    )


sys.excepthook = excepthook


def michelson_interpreter(code: list):
    CR = _variables.CURRENT_RUN

    for i in code:
        if isinstance(i, list):
            if i[-1]["prim"] == "IF":
                process_ifmacro(i)
            else:
                process_unpairmacro(i)
        else:
            step = process_instruction(i, CR.stack)
            if step is not None and "IF" not in i["prim"]:
                CR.steps.append(step)

    CR.current_path_constraint.processed = (
        CR.current_path_constraint.satisfiable
    ) = CR.executed = True


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
def main(
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
    # Parsing the script
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

    # Initial run
    CR = _variables.CURRENT_RUN = _types.Run()
    _variables.RUNS.append(CR)

    # Setting up
    ## State
    CR.current_state = _types.State(
        account, address, amount, balance, entrypoint, gas_limit, _id, timestamp
    )
    CR.states.append(CR.current_state)
    ## Initial pair
    CR.stack.append(
        initialize(
            parameter_type["args"][0], parameter, storage_type["args"][0], storage
        )
    )
    ## PCT
    CPC = CR.current_path_constraint = _types.PathConstraint()

    CR.path_constraints.append(CPC)
    ## Adding the initial `pair` as a bool here
    CPC.input_variables = {
        CR.stack[0].name: CR.symbolic_variables.get(
            CR.stack[0].name, z3.Bool(CR.stack[0].name)
        )
    }
    ## + adding whatever's inside that `pair` + state variables
    CPC.input_variables.update(
        {
            x.name: CR.symbolic_variables.get(x.name, z3.Bool(x.name))
            for x in _functions.find_nested(CR.stack[0])
            + [
                _functions.applyAMOUNT({}, None, deque()),
                _functions.applyBALANCE({}, None, deque()),
                _functions.applyCHAIN_ID({}, None, deque()),
                _functions.applyNOW({}, None, deque()),
                _functions.applySELF({}, None, deque()),
                _functions.applySENDER({}, None, deque()),
                _functions.applySOURCE({}, None, deque()),
            ]
        }
    )
    ## Adding initial `pair` as the first step
    CR.steps.append(
        _types.Step(
            _types.Delta([], [CR.stack[0]]),
            [parameter_type, storage_type],
            list(copy.deepcopy(CR.stack)),
        )
    )

    # Execution
    michelson_interpreter(code)

    # Inspection of path constraints
    s = z3.Solver()
    pct = [
        {
            "predicates": CR.current_path_constraint.predicates,
            "sat": CR.current_path_constraint.satisfiable,
        }
    ]
    for i in CR.path_constraints[1:]:
        s.add(i.predicates)
        i.satisfiable = True if s.check() == z3.sat else False
        pct.append({"predicates": i.predicates, "sat": i.satisfiable})
        if i.satisfiable:
            r = copy.deepcopy(CR)
            _variables.RUNS.append(r)
            # Preprocessing
            r.stack.clear()
            r.path_constraints.clear()
            r.steps.clear()
            r.executed = False
            r.stack.append(copy.deepcopy(CR.concrete_variables["pair_0"]))
            r.concrete_variables = {r.stack[0].name: r.stack[0]}
            r.concrete_variables.update(
                {x.name: x for x in _functions.find_nested(r.stack[0])}
            )
            r.concrete_variables.update(
                {
                    x: copy.deepcopy(CR.concrete_variables[x])
                    for x in CR.concrete_variables.keys()
                    if x.startswith("sv_")
                }
            )
            for i in s.model():
                if i.name().startswith("sv_"):  # type: ignore
                    match i.name().split("_")[1]:  # type: ignore
                        case "amount" | "balance":
                            setattr(
                                r.current_state,
                                "amount",
                                (s.model()[CR.symbolic_variables[i.name()]]).as_long(),  # type: ignore
                            )
                            setattr(
                                r.current_state,
                                "balance",
                                (s.model()[CR.symbolic_variables[i.name()]]).as_long(),  # type: ignore
                            )
                        case "now":
                            setattr(
                                r.current_state,
                                "timestamp",
                                (s.model()[CR.symbolic_variables[i.name()]]).as_long(),  # type: ignore
                            )
                        case "self":
                            r.concrete_variables[i.name()].value[0].value = [  # type: ignore
                                str(s.model()[CR.symbolic_variables[i.name()]])  # type: ignore
                            ]
                            setattr(
                                r.current_state,
                                "address",
                                str(s.model()[CR.symbolic_variables[i.name()]]),  # type: ignore
                            )
                            continue
                        case "sender" | "source":
                            setattr(
                                r.current_state,
                                "address",
                                str(s.model()[CR.symbolic_variables[i.name()]]),  # type: ignore
                            )
                        case _:
                            continue
                r.concrete_variables[i.name()].value = [str(s.model()[CR.symbolic_variables[i.name()]])]  # type: ignore
            r.symbolic_variables = {r.stack[0].name: z3.Bool(r.stack[0].name)}
            r.symbolic_variables.update(
                {
                    x: copy.deepcopy(CR.symbolic_variables[x])
                    for x in CR.current_path_constraint.input_variables.keys()
                }
            )
            r.path_constraints.append(_types.PathConstraint())
            r.path_constraints[0].input_variables = copy.deepcopy(r.symbolic_variables)
            r.current_path_constraint = r.path_constraints[0]
            r.variable_names = {
                x: {
                    int(y.split("_")[1])
                    for y in r.current_path_constraint.input_variables.keys()
                    if y.startswith(x)
                }
                for x in set(
                    [
                        z.split("_")[0]
                        for z in r.current_path_constraint.input_variables.keys()
                        if not z.startswith("sv_")
                    ]
                )
            }
        s.reset()
    print(
        json.dumps(pct, default=lambda x: str(x) if isinstance(x, z3.Z3PPObject) else x)
    )


if __name__ == "__main__":
    main()
