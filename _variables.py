#!/usr/bin/python3
from collections import deque
from typing import Deque, List

from _types import Data, PathConstraint, State, Step

CURRENT_STATE: State = State()
CURRENT_PATH_CONSTRAINT: PathConstraint
STACK: Deque[Data] = deque()
STATES: List[State] = []
STEPS: List[Step] = []
PATH_CONSTRAINTS: List[PathConstraint] = []
