from dataclasses import dataclass, field
from typing import Union, List, Optional

from src.interaction.goals import Goal, parse_goals
from src.mwe import Mwe

_REPL_PROMPT = "REPL>"


@dataclass(frozen=True)
class TacticState:
    pretty_print: str
    identity: int = field(compare=False)
    message: Optional[str] = field(default=None, compare=False)
    goals: List[Goal] = field(init=False, compare=False, repr=False)

    def __post_init__(self) -> None:
        goals = parse_goals(self.pretty_print)
        assert len(goals) == self.pretty_print.count("⊢")
        object.__setattr__(self, "goals", goals)

    @property
    def num_goals(self) -> int:
        return len(self.goals)


@dataclass(frozen=True)
class ProofFinished:
    tactic_state_id: int
    message: Optional[str] = field(default=None, compare=False)


@dataclass(frozen=True)
class ProofGivenUp:
    pass


@dataclass(frozen=True)
class LeanError:
    error: str


TacticResult = Union[
    TacticState,
    ProofFinished,
    LeanError,
    TimeoutError,
    ProofGivenUp,
]


class GymCrashError(Exception):
    @property
    def is_out_of_memory(self) -> bool:
        return str(self) == "OOM"


class GymHardTimeoutError(Exception):
    pass


class GymInitError(Exception):
    pass


class InteractionGym:
    """Gym-like environment for programmatic interaction with Lean through tactics or commands."""

    mwe: Mwe

    def __init__(
        self,
        mwe: Mwe,
    ):
        """Initialize Gym."""
        self.mwe = mwe
