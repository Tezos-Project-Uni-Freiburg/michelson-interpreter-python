#!/usr/bin/python3
from collections import deque
from typing import Deque, List

from _types import Data, State, Step

CURRENT_STATE: State = State()
STACK: Deque[Data] = deque()
STATES: List[State] = []
STEPS: List[Step] = []
