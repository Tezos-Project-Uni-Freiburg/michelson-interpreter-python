#!/usr/bin/python3
import copy
import dataclasses
import json
import re
import subprocess
import sys

import click

import _types
import _variables
from _functions import flatten, initialize, process_instruction


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
    _variables.CURRENT_STATE = _types.State(
        account, address, amount, entrypoint, gas_limit, _id, timestamp
    )
    _variables.CURRENT_PATH_CONSTRAINT = _types.PathConstraint()
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
        flatten(
            flatten(s[2]["args"], skip_ifs=True), skip_ifs=True
        ),  # TODO: outer `flatten` seems to be just to make sure, could find a better way for this
    )

    _variables.STACK.append(
        initialize(
            parameter_type["args"][0], parameter, storage_type["args"][0], storage
        )
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
            # TODO: definitely the most inefficient-looking part of the codebase
            op = ""
            if i[0]["prim"] == "COMPARE":
                _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
                    [
                        _types.SYMBOLIC_VARIABLES[_variables.STACK[-1].name],
                        _types.SYMBOLIC_VARIABLES[_variables.STACK[-2].name],
                    ]
                )
                match i[1]["prim"]:
                    case "EQ":
                        op = "=="
                    case "GE":
                        op = ">="
                    case "GT":
                        op = ">"
                    case "LE":
                        op = "<="
                    case "LT":
                        op = "<"
                    case "NEQ":
                        op = "!="
                    case _:
                        ...
                _variables.CURRENT_PATH_CONSTRAINT.predicates.append(
                    f"{_variables.CURRENT_PATH_CONSTRAINT.initial_variables[0]} {op} {_variables.CURRENT_PATH_CONSTRAINT.initial_variables[1]}"
                )
                # Need to execute COMPARE here
                ...
            else:
                _variables.CURRENT_PATH_CONSTRAINT.initial_variables.append(
                    _types.SYMBOLIC_VARIABLES[_variables.STACK[-1].name]
                )
                match i[0]["prim"]:
                    case "EQ":
                        op = "=="
                    case "GE":
                        op = ">="
                    case "GT":
                        op = ">"
                    case "LE":
                        op = "<="
                    case "LT":
                        op = "<"
                    case "NEQ":
                        op = "!="
                    case _:
                        ...
                _variables.CURRENT_PATH_CONSTRAINT.predicates.append(
                    f"{_variables.CURRENT_PATH_CONSTRAINT.initial_variables[0]} {op} 0"
                )
                ...
            # Need to start recording whatever happens to this variable
            # _variables.CURRENT_PATH_CONSTRAINT.initial_variables = (
            #     [_types.SYMBOLIC_VARIABLES[_variables.STACK[-1].name]]
            # )
            # for j in i:  # these are the actual instructions
            #     match j["prim"]:
            #         # Need to check that there are enough variables of acceptable types
            #         case "COMPARE":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-2].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             r = int(_variables.STACK[-1].value[0])
            #             op = "<" if r == -1 else ">" if r == 1 else "=="
            #             _variables.CURRENT_PATH_CONSTRAINT.predicates.append(
            #                 f"{_variables.CURRENT_PATH_CONSTRAINT.initial_variables[0]} {op} {_variables.CURRENT_PATH_CONSTRAINT.initial_variables[1]}"
            #             )
            #         case "EQ":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             # parameters[0].value[0].lower() == "true"

            #             ...
            #         case "GE":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             ...
            #         case "GT":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             ...
            #         case "LE":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             ...
            #         case "LT":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             ...
            #         case "NEQ":
            #             if (
            #                 len(_variables.CURRENT_PATH_CONSTRAINT.initial_variables)
            #                 == 0
            #             ):
            #                 _variables.CURRENT_PATH_CONSTRAINT.initial_variables.extend(
            #                     [
            #                         _types.SYMBOLIC_VARIABLES[
            #                             _variables.STACK[-1].name
            #                         ],
            #                     ]
            #                 )
            #             step = process_instruction(j, _variables.STACK)
            #             if step is not None and "IF" not in j["prim"]:
            #                 _variables.STEPS.append(step)
            #             ...
            #         case _:
            #             # IF should be caught here (or maybe below this?)
            #             ...
            # ...
        else:
            step = process_instruction(i, _variables.STACK)
            if step is not None and "IF" not in i["prim"]:
                _variables.STEPS.append(step)

    print(json.dumps([dataclasses.asdict(x) for x in _variables.STEPS]))


if __name__ == "__main__":
    michelson_interpreter()
