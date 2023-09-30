import os
import json

from typing import Optional, Any, List, Dict
from pathlib import Path

import humps


from src.lean_env.execution_env import ExecutionEnv
from src.mwe import Mwe


class PosEncoding:
    line: int
    column: int

    def __init__(
        self,
        line: int,
        column: int,
    ):
        self.line = line
        self.column = column

    def __eq__(self, other: object) -> bool:
        if isinstance(other, PosEncoding):
            return self.line == other.line and self.column == other.column
        return False


class Premise:
    pos: PosEncoding
    mod_name: str
    full_name: str
    end_pos: PosEncoding
    def_pos: PosEncoding
    def_end_pos: PosEncoding

    def __init__(
        self,
        pos: Dict[str, int],
        mod_name: str,
        full_name: str,
        end_pos: Dict[str, int],
        def_pos: PosEncoding,
        def_end_pos: PosEncoding,
    ):
        self.pos = PosEncoding(**pos)
        self.mod_name = mod_name
        self.full_name = full_name
        self.end_pos = PosEncoding(**end_pos)
        self.def_pos = def_pos
        self.def_end_pos = def_end_pos


class TracedTacticState:
    state_before: str
    state_after: str
    pos: int
    end_pos: int

    def __init__(
        self,
        state_before: str,
        state_after: str,
        pos: int,
        end_pos: int,
    ):
        self.state_before = state_before
        self.state_after = state_after
        self.pos = pos
        self.end_pos = end_pos

    def is_tactic_finishing_proof(self) -> bool:
        if self.state_after.find("no goals") != -1:
            return True
        return False


class AstContent:
    tatics: List[TracedTacticState]
    premises: List[Premise]
    command_as_ts: List[Any]

    def __init__(
        self,
        tactics: List[Any],
        premises: List[Any],
        command_as_ts: List[Any],
    ):
        self.tatics = list(map(lambda tac: TracedTacticState(**tac), tactics))
        self.premises = list(map(lambda pre: Premise(**pre), premises))
        self.command_as_ts = command_as_ts


class Tracer:
    def __init__(
        self,
        mwe: Mwe,
        tmp_dir: Optional[Path] = None,
    ):
        """Initialize Tracer."""
        self.mwe = mwe
        self.execution_env = ExecutionEnv(tmp_dir)
        self.execution_env.write_main_file(mwe.code)
        self.tracing_result: Optional[AstContent] = None

    def trace_mwe(self) -> None:
        self.execution_env.create_env()
        self.execution_env.write_main_file(self.mwe.code)
        os.chdir(self.execution_env.tmp_dir)
        command = f"lake env lean --threads 1 --run \
            ExtractData.lean {self.execution_env.tmp_dir}/Main.lean"
        os.system(command)
        path = self.execution_env.tmp_dir / "build/ir/Main.ast.json"
        self.load_trace_result(path)

    def load_trace_result(self, path: Path) -> None:
        with open(path, "r", encoding="utf-8") as file:
            data = json.load(file)
        data = humps.decamelize(data)
        content = AstContent(**data)
        self.tracing_result = content

    def get_traced_tactic(
        self, tactics: List[TracedTacticState]
    ) -> List[TracedTacticState]:
        """Get the tactics that are within the theorem."""

        code_bytes = self.mwe.code.encode("utf-8")
        theorem_code = (
            self.mwe.code[self.mwe.theorem_start : self.mwe.proof_end]
        ).encode("utf-8")
        theorem_start_pos = code_bytes.find(theorem_code)
        assert theorem_start_pos != -1
        theorem_end_pos = theorem_start_pos + len(theorem_code)
        # Only consider tactics that are within the theorem.
        tactics = [
            tactic
            for tactic in tactics
            if tactic.pos in range(theorem_start_pos, theorem_end_pos)
        ]
        # Some tactics are listed double - the normal tactic + the tactic within a tactic.
        j = 0
        while j < len(tactics):
            i = 0
            while i < len(tactics):
                if i == j:
                    i += 1
                    continue
                if (
                    tactics[i].pos >= tactics[j].pos
                    and tactics[i].end_pos <= tactics[j].end_pos
                ):
                    tactics.remove(tactics[i])
                    i -= 1
                i += 1
            j += 1
        return tactics

    def get_premises_from_tactic(self, tactic: TracedTacticState) -> List[Premise]:
        """Get the premises that are used in the tactic."""
        assert self.tracing_result is not None

        used_premises = []
        for premise in self.tracing_result.premises:
            code_splitted = self.mwe.code.split("\n")
            code_before_premises = "\n".join(code_splitted[0 : premise.pos.line - 1])
            string_pos = (
                len(code_before_premises.encode("utf-8")) + premise.end_pos.column
            )
            if string_pos in range(tactic.pos, tactic.end_pos):
                used_premises.append(premise)
        return used_premises
