#!/usr/bin/python3
import operator
from collections import deque
from typing import Deque, List

from _types import Data, PathConstraint, State, Step

# Variables
CURRENT_STATE: State = State()
CURRENT_PATH_CONSTRAINT: PathConstraint
STACK: Deque[Data] = deque()
STATES: List[State] = []
STEPS: List[Step] = []
PATH_CONSTRAINTS: List[PathConstraint] = []
UNPAIR_FLAG: bool = False

# Constants
OPS = {
    "EQ": operator.eq,
    "GE": operator.ge,
    "GT": operator.gt,
    "LE": operator.le,
    "LT": operator.lt,
    "NEQ": operator.ne,
}
