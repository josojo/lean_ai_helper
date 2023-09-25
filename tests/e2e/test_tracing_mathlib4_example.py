import pytest

from loguru import logger

from src.mwe import Mwe
from src.trace.trace import AstContent, Tracer


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""

    code = ""
    with open("tests/data/Mathlib.Meta.NormNum.Prime.lean", "r", encoding="utf-8") as file:
        code = file.read()

    logger.debug("code len: " + str(len(code)))
    mwe = Mwe(
        code,
        "minFacHelper_0",
    )
    tracer = Tracer(mwe)
    ast_content = tracer.trace_mwe()
    assert isinstance(ast_content, AstContent)
    assert len(ast_content.tatics) == 17
    code = code.encode("utf-8")
    tactic = ast_content.tatics[0]
    tatic_code = (code[tactic.pos : tactic.end_pos]).decode("utf-8")
    assert tatic_code == "have : 2 < minFac n := h.1.trans_le h.2.2"
