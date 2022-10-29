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
{value.args[0]}
-------------------------------
Content of the exception:
{json.dumps(value.args[1] if len(value.args) > 1 else [])}
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
    try:
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
    except Exception as e:
        if isinstance(e, _types.CustomException):
            CR.current_path_constraint.satisfiable = False
            CR.current_path_constraint.reason = e
        else:
            print("Unknown exception! Details below:")
            print(e)
            print(CR.steps)
            raise e
    else:
        CR.current_path_constraint.satisfiable = True
    CR.current_path_constraint.processed = CR.executed = True


def process_run():
    CR = _variables.CURRENT_RUN
    _variables.REMAINING_RUNS.remove(CR)
    _variables.EXECUTED_RUNS.append(CR)
    s = z3.Solver()
    for i in CR.path_constraints[1:]:
        if (
            len(
                [
                    True
                    for x in _variables.EXECUTED_RUNS
                    if set(i.predicates).issubset(
                        set(x.current_path_constraint.predicates)
                    )
                ]
            )
            != 0
        ):
            continue
        s.add(i.predicates)
        i.satisfiable = True if s.check() == z3.sat else False
        if i.satisfiable:
            r = copy.deepcopy(CR)
            _variables.REMAINING_RUNS.append(r)
            # Preprocessing
            r.stack.clear()
            r.path_constraints.clear()
            r.steps.clear()
            r.executed = False
            # Variable generation
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
                    or (
                        CR.concrete_variables[x].parent
                        and CR.concrete_variables[x].parent.startswith("sv_")  # type: ignore
                    )
                }
            )
            # Value update
            for j in s.model():
                if j.name() not in CR.symbolic_variables:  # type: ignore
                    continue
                if j.name().startswith("sv_"):  # type: ignore
                    match j.name().split("_")[1]:  # type: ignore
                        case "amount" | "balance":
                            r.current_state.amount = s.model()[CR.symbolic_variables[j.name()]].as_long()  # type: ignore
                            r.current_state.balance = s.model()[CR.symbolic_variables[j.name()]].as_long()  # type: ignore
                        case "now":
                            r.current_state.timestamp = s.model()[CR.symbolic_variables[j.name()]].as_long()  # type: ignore
                        case "sender" | "source":
                            r.current_state.address = str(s.model()[CR.symbolic_variables[j.name()]])  # type: ignore
                        case _:
                            continue
                match j.name().split("_")[0]:  # type: ignore
                    case "or":
                        # _variables.CREATE_VARIABLE = True
                        if str(s.model()[CR.symbolic_variables[j.name()]]).lower() == "true":  # type: ignore
                            r.concrete_variables[j.name()].or_value = "Left"  # type: ignore
                            # r.concrete_variables[j.name()].value = [_types.Data(r.concrete_variables[j.name()].or_type[0], ["0"], j.name())]  # type: ignore
                        else:
                            r.concrete_variables[j.name()].or_value = "Right"  # type: ignore
                            # r.concrete_variables[j.name()].value = [_types.Data(r.concrete_variables[j.name()].or_type[1], ["0"], j.name())]  # type: ignore
                        # _variables.CREATE_VARIABLE = False
                    case "option":
                        if str(s.model()[CR.symbolic_variables[j.name()]]).lower() == "true":  # type: ignore
                            r.concrete_variables[j.name()].option_value = "None"  # type: ignore
                            for k in r.concrete_variables[j.name()].value:  # type: ignore
                                r.concrete_variables.pop(k.name)
                                r.symbolic_variables.pop(k.name)
                            r.concrete_variables[j.name()].value.clear()  # type: ignore
                        else:
                            r.concrete_variables[j.name()].option_value = "Some"  # type: ignore
                            # _variables.CREATE_VARIABLE = True
                            # r.concrete_variables[j.name()].value = [_types.Data(r.concrete_variables[j.name()].option_type[0], [], j.name())]  # type: ignore
                            # _variables.CREATE_VARIABLE = False
                    case "pair":
                        continue
                    case _:
                        r.concrete_variables[j.name()].value = [str(s.model()[CR.symbolic_variables[j.name()]])]  # type: ignore
            r.ephemeral_predicates.clear()
            r.ephemeral_variables.clear()
            r.symbolic_variables = copy.deepcopy(CR.symbolic_variables)
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
    _variables.REMAINING_RUNS.append(CR)

    # Setting up
    ## State
    CR.current_state = _types.State(
        account, address, amount, balance, entrypoint, gas_limit, _id, timestamp
    )
    CR.states.append(CR.current_state)
    ## Initial pair
    _variables.CREATE_VARIABLE = True
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
                _functions.applySENDER({}, None, deque()),
                _functions.applySOURCE({}, None, deque()),
            ]
        }
    )
    _variables.CREATE_VARIABLE = False
    ## Adding initial `pair` as the first step
    CR.steps.append(
        _types.Step(
            _types.Delta([], [CR.stack[0]]),
            [parameter_type, storage_type],
            list(copy.deepcopy(CR.stack)),
        )
    )

    # Execution
    michelson_interpreter(copy.deepcopy(code))

    # Run processing
    while len(_variables.REMAINING_RUNS) != 0:
        process_run()
        # TODO: really ugly and unnecessary
        if len(_variables.REMAINING_RUNS) != 0:
            CR = _variables.CURRENT_RUN = _variables.REMAINING_RUNS[0]
        else:
            continue
        michelson_interpreter(copy.deepcopy(code))
    print(
        json.dumps(
            {
                _variables.EXECUTED_RUNS.index(x): {
                    "predicates": x.current_path_constraint.predicates,
                    "sat": x.current_path_constraint.satisfiable,
                    "reason": x.current_path_constraint.reason.args
                    if x.current_path_constraint.reason
                    else None,
                }
                for x in _variables.EXECUTED_RUNS
            },
            default=lambda x: str(x)
            if isinstance(x, z3.Z3PPObject) and x.use_pp()
            else x,
        )
    )


if __name__ == "__main__":
    main()
