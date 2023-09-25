import os
import json

from typing import Optional, Any, List
from pathlib import Path

import humps


from src.lean_env.execution_env import ExecutionEnv
from src.mwe import Mwe


class TacticState:
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


class AstContent:
    tatics: List[TacticState]

    def __init__(
        self,
        tactics: List[Any],
        premises: List[Any],
        command_as_ts: List[Any],
    ):
        self.tatics = list(map(lambda tac: TacticState(**tac), tactics))
        self.premises = premises
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

    def trace_mwe(self) -> AstContent:
        self.execution_env.create_env()
        self.execution_env.write_main_file(self.mwe.code)
        os.chdir(self.execution_env.tmp_dir)
        command = f"lake env lean --threads 1 --run \
            ExtractData.lean {self.execution_env.tmp_dir}/Main.lean"
        os.system(command)
        path = self.execution_env.tmp_dir / "build/ir/Main.ast.json"
        with open(path, "r", encoding="utf-8") as file:
            data = json.load(file)
        data = humps.decamelize(data)
        content = AstContent(**data)
        return content
