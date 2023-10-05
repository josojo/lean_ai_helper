"""Gym-like environment for programmatic interaction with Lean through tactics or commands.
"""
import os
import json
import shlex
import subprocess
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Union, List, Optional, Tuple, Dict
from loguru import logger

from src.lean_env.execution_env import ExecutionEnv
from src.mwe import Mwe
from src.interaction.utils import format_tactic_for_repl
from src.state.goals import Goal, parse_goals
from src.trace.trace import TracedTacticState

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


class SubmoduleNotFoundError(Exception):
    """Raised when the required submodules are not found."""


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


class Gym:
    """Gym-like environment for programmatic interaction with Lean through tactics or commands."""

    mwe: Mwe

    def __init__(
        self,
        mwe: Mwe,
        tactic: Optional[TracedTacticState] = None,
        tmp_dir: Optional[Path] = None,
    ):
        """Initialize Gym."""
        self.mwe = mwe
        self.tactic: Optional[TracedTacticState] = tactic
        self.proc: Optional[subprocess.Popen[str]] = None
        self.execution_env = ExecutionEnv(tmp_dir)
        self.is_crashed = False

    def __enter__(self) -> Tuple["Gym", TacticState]:
        """Initialize Dojo."""
        logger.debug(f"Initializing Gym for {self.mwe.name}")
        try:
            self.execution_env.create_env()
            self.execution_env.write_main_file(self._modify_proof())
            os.chdir(self.execution_env.tmp_dir)

            # Build the common repl tactic in a separate git repo and
            # copy the bin files into the traced repo
            cmd = "lake env lean Main.lean"
            self.proc = subprocess.Popen(
                shlex.split(cmd),
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                universal_newlines=True,
                encoding="utf-8",
                bufsize=1,
            )
            # Get the initial tactic state.
            try:
                res = json.loads(self._read_next_line()[0])
                logger.debug(f"Response: {res}")
            except EOFError as exc:
                raise GymInitError("EOF") from exc
            except json.JSONDecodeError:
                logger.error("Failed to parse JSON response")
                raise
            except Exception as ex:
                logger.error(f"Unexpected error: {ex}")
                raise

            assert res["error"] is None
            assert res["tacticState"] != "no goals"
            init_state = TacticState(
                self._post_process(res["tacticState"]),
                res["sid"],
            )

            return self, init_state

        except Exception as ex:
            raise ex

    def run_tac(self, state: TacticState, tactic: str) -> TacticResult:
        if not isinstance(state, TacticState):
            raise RuntimeError(
                f"Attempting to run a tactic on an invalid state {state}."
            )

        assert isinstance(tactic, str), f"Invalid tactic {tactic}"

        tsid = state.identity

        tactic_array = format_tactic_for_repl(tactic)
        return self._submit_tactics(tsid, tactic_array)

    def run_tacs(self, state: TacticState, tactics: List[str]) -> TacticResult:
        if not isinstance(state, TacticState):
            raise RuntimeError(
                f"Attempting to run a tactic on an invalid state {state}."
            )

        tsid = state.identity
        return self._submit_tactics(tsid, tactics)

    def _submit_tactics(self, tsid: int, tactics: List[str]) -> TacticResult:
        req = json.dumps({"sid": tsid, "cmd": tactics})
        res = self._submit_request(req)

        if res["error"] is not None:
            if "proof contains `sorry`" in res["error"]:
                return ProofGivenUp()
            if "try_for_time tactic failed, timeout" in res["error"]:
                return TimeoutError(res["error"].strip())
            return LeanError(res["error"].strip())
        if res["tacticState"] == "no goals":
            return ProofFinished(res["sid"], res["message"])
        tactic_state = self._post_process(res["tacticState"])
        return TacticState(
            tactic_state,
            res["sid"],
            res["message"],
        )

    def _post_process(self, tactic_state: str) -> str:
        """Post-process the pretty-printed tactic state.

        Args:
            tactic_state (str): _description_

        Returns:
            str: _description_
        """
        match = re.match(r"\d+ goals\n", tactic_state)
        if match is not None:
            return tactic_state[match.end() :]
        return tactic_state

    def _modify_proof(self) -> str:
        # Modify the proof and set up the `repl` tactic.
        code_proof = "\n  by\n  lean_dojo_repl\n  sorry\n"
        code_before_theorem = self.mwe.code[: self.mwe.theorem_start]
        code_thereom = ""
        if self.tactic is None:
            code_thereom = self.mwe.code[self.mwe.theorem_start : self.mwe.proof_start]
            modified_code = (
                "import Lean4Repl\n\n"
                + code_before_theorem
                + code_thereom
                + code_proof
                + self.mwe.code[self.mwe.proof_end :]
            )
        else:  # Modify the proof to start from the given tactic.
            code_as_bytes = self.mwe.code.encode("utf-8")
            code_cutted_of_at_tactic = code_as_bytes[: self.tactic.pos].decode("utf-8")
            code_thereom = (
                code_cutted_of_at_tactic[self.mwe.theorem_start :]
                + "lean_dojo_repl\n sorry\n"
            )
            modified_code = (
                "import Lean4Repl\n\n"
                + code_before_theorem
                + "set_option maxHeartbeats 0 in\n"
                + code_thereom
                + self.mwe.code[self.mwe.proof_end :]
            )
        return modified_code

    def _read_next_line(self) -> Tuple[str, str]:
        """Read the next line from `self.proc`.

        Raises:
            EOFError: _description_
            DojoCrashError: _description_
            DojoInitError: _description_

        Returns:
            str: _description_
        """
        if self.proc is None:
            raise RuntimeError("self.proc is not initialized")
        if self.proc.stdout is None:
            raise RuntimeError("self.proc.stout is not initialized")
        msg: List[str] = []
        while True:
            line = self.proc.stdout.readline().strip()
            if line == "":
                raise EOFError
            if line.startswith(_REPL_PROMPT):
                self._check_alive()
                return line[len(_REPL_PROMPT) :].strip(), "\n".join(msg)
            if "error: " in line:
                if (
                    "error: deep recursion was detected" in line
                    or "error: [fatal] not_a_theorem" in line
                ):
                    self.is_crashed = True
                    raise GymCrashError(line)
                if "error: unknown package" in line:
                    self.is_crashed = True
                    raise GymInitError(line)
            msg.append(line)

    def _check_alive(self) -> None:
        """Check if the process is still alive."""
        if self.proc is None:
            raise RuntimeError("self.proc is not initialized")
        exit_code = self.proc.poll()
        if exit_code is None:
            return
        if exit_code == 137:
            raise GymCrashError("OOM")
        raise GymCrashError(f"Unknown exit code: {exit_code}")

    def _submit_request(self, req: str) -> Dict[str, str]:
        """Submit a request to Lean and get the response.

        Args:
            req (str): _description_

        Raises:
            DojoCrashError: _description_

        Returns:
            Dict[str, Any]: _description_
        """
        logger.debug(f"Request: {req}")
        if self.proc is None:
            raise RuntimeError("self.proc is not initialized")
        if self.proc.stdin is None:
            raise RuntimeError("self.proc.stdin is not initialized")
        self._check_alive()
        self.proc.stdin.write(req + "\n")
        try:
            res, msg = self._read_next_line()
            logger.debug(f"Response: {res}")
        except EOFError as exc:
            raise GymCrashError("EOF") from exc
        try:
            result: Dict[str, str] = json.loads(res)
        except json.decoder.JSONDecodeError as exc:
            raise GymCrashError(f"Invalid JSON: {res}") from exc

        assert "message" not in result
        result["message"] = msg
        return result

    def __exit__(self, _exc_type: None, _exc_val: None, _exc_tb: None) -> None:
        """Exit Gym."""

        if not self.is_crashed:
            req = "exit"
            try:
                self._submit_request(req)
            except (GymCrashError, json.decoder.JSONDecodeError):
                pass
        else:
            logger.error(
                f"Crashed gym instance can not be cleanly shut down: {self.is_crashed}"
            )
