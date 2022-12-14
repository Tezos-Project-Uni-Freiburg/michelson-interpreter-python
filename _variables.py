#!/usr/bin/python3
from __future__ import annotations

from typing import List

from pysmt.shortcuts import GE, GT, LE, LT, EqualsOrIff, NotEquals

from _types import Run

# Variables
CURRENT_RUN: Run
EXECUTED_RUNS: List[Run] = []
REMAINING_RUNS: List[Run] = []
UNPAIR_FLAG: bool = False
CREATE_VARIABLE: bool = False

# Constants
OPS = {
    "EQ": EqualsOrIff,
    "GE": GE,
    "GT": GT,
    "LE": LE,
    "LT": LT,
    "NEQ": NotEquals,
}
