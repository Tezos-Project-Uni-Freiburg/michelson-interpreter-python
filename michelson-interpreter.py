#!/usr/bin/python3
import io
import json
import pprint
import re
import subprocess
import sys

import click

from _types import Delta, State, Step
import _functions


def excepthook(type, value, traceback):
    ...


sys.excepthook = excepthook


def michelson_interpreter(
    script: io.TextIOWrapper, parameter: str, storage: str, state: State
):
    global current_state
    current_state = state
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
    p_raw, s_raw, c_raw = s[0], s[1], s[2]
    pprint.pp(p_raw)


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as f:
        michelson_interpreter(f, "...", "...", State())
