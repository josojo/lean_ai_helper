"""Gym-like environment for programmatic interaction with Lean through tactics or commands.
"""
import os
import json
import shlex
import shutil
import subprocess
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Union, List, Optional, Tuple, Dict
from loguru import logger

from src.interaction.goals import Goal, parse_goals
from src.mwe import Mwe
from src.interaction.utils import format_tatic_for_repl

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
        tmp_dir: Optional[Path] = None,
    ):
        """Initialize Gym."""
        self.mwe = mwe
        self.proc: Optional[subprocess.Popen[str]] = None
        if tmp_dir is None:
            self.tmp_dir = Path().cwd() / "execution_env"
            logger.debug(f"Using default tmp_dir: {self.tmp_dir}")
        else:
            self.tmp_dir = tmp_dir
        self.is_crashed = False

    def __enter__(self) -> Tuple["Gym", TacticState]:
        """Initialize Dojo."""
        logger.debug(f"Initializing Gym for {self.mwe.name}")
        try:
            self._create_test_env()
            os.chdir(self.tmp_dir)

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

        tactic_array = format_tatic_for_repl(tactic)
        req = json.dumps({"sid": tsid, "cmd": tactic_array})
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

    def _create_test_env(self) -> None:
        """Create a test environment for the proof."""

        # copy the content from common repl dir into the tmp dir

        if not os.path.exists(self.tmp_dir):
            logger.debug("Copying the content from submodule repl dir into the tmp dir")
            shutil.copytree(
                str(Path.cwd() / "Lean4Repl"),
                str(self.tmp_dir) + "/",
                dirs_exist_ok=True,
            )
            os.chdir(self.tmp_dir)
            command = "lake exe cache get"
            subprocess.run(command.split(), check=True)
            command = "lake build Lean4Repl"
            subprocess.run(command.split(), check=True)

        # Interaction through tactics.
        modified_code = self._modify_proof()
        repl_file = "Main.lean"
        repl_dst = self.tmp_dir / repl_file
        with repl_dst.open("wt") as oup:
            oup.write(modified_code)

    def _modify_proof(self) -> str:
        # Modify the proof and set up the `repl` tactic.
        code_proof = "\nby\n  lean_dojo_repl\n  sorry\n"
        code_before_theorem = self.mwe.code[: self.mwe.theorem_start]
        code_thereom = self.mwe.code[self.mwe.theorem_start : self.mwe.proof_start]
        modified_code = (
            "import Lean4Repl\n\n"
            + code_before_theorem
            + "set_option maxHeartbeats 0 in\n"
            + code_thereom
            + code_proof
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
            logger.debug(line)
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

        logger.debug(f"Exiting GYM for {self.mwe.name}")