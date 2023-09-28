import pytest
import os

from loguru import logger

from src.mwe import Mwe
from src.trace.trace import AstContent, Tracer


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""

    code = ""
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(script_dir, "../data/Mathlib.Meta.NormNum.Prime.lean")

    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    mwe = Mwe(
        code,
        "minFacHelper_0",
    )
    tracer = Tracer(mwe)
    ast_content = tracer.trace_mwe()
    assert isinstance(ast_content, AstContent)
    assert len(ast_content.tatics) == 17

    # Check tactics
    code = code.encode("utf-8")
    tactic = ast_content.tatics[0]
    tatic_code = (code[tactic.pos : tactic.end_pos]).decode("utf-8")
    assert tatic_code == "have : 2 < minFac n := h.1.trans_le h.2.2"

    # Check premises
    premise = ast_content.premises[-1]
    assert premise.mod_name == "Init.Core"
    assert premise.full_name == "Iff.mp"
    assert premise.pos == {"line": 41, "column": 41}
    assert premise.end_pos == {"line": 41, "column": 42}
    assert premise.def_pos == {"line": 90, "column": 2}