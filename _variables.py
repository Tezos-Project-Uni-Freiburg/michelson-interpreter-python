#!/usr/bin/python3
from __future__ import annotations

import operator
from typing import List

from _types import Run

# Variables
CURRENT_RUN: Run
EXECUTED_RUNS: List[Run] = []
REMAINING_RUNS: List[Run] = []
# UNPAIR_FLAG: bool = False
CREATE_VARIABLE: bool = False

# Constants
OPS = {
    "EQ": operator.eq,
    "GE": operator.ge,
    "GT": operator.gt,
    "LE": operator.le,
    "LT": operator.lt,
    "NEQ": operator.ne,
}
