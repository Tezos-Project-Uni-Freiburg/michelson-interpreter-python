#!/usr/bin/python3
import json
import re
import subprocess
import sys

import click

from _types import Delta, State, Step
import _functions


def excepthook(type, value, traceback):
    ...


sys.excepthook = excepthook


def michelson_interpreter(script, parameter, storage, state):
    s_raw = subprocess.run(
        ["./ext/michelson-parser-wrapper/bin/michelson-parser.js"],
        capture_output=True,
        encoding="utf-8",
        stdin=script,
    )
    s = json.loads(re.sub(r"\\\\\"", '\\"', s_raw.stdout).strip()[1:-1])
    if len(s) > 1:
        raise Exception("Multiple parsings!")
    s = json.loads(s[0])


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        michelson_interpreter(f, ..., ..., ...)
