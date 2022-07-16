#!/usr/bin/python3
import pprint
import subprocess
import sys

import click

from _types import Delta, State, Step
import _functions


def excepthook(type, value, traceback):
    ...


sys.excepthook = excepthook


def michelson_interpreter(script, parameter, storage, state):
    s = subprocess.run(
        ["./ext/michelson-parser-wrapper/bin/michelson-parser.js"],
        capture_output=True,
        encoding="utf-8",
        stdin=script,
    )
    pprint.pprint(s)


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        michelson_interpreter(f, ..., ..., ...)
