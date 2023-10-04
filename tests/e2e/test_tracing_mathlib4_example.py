import os

from loguru import logger

from src.mwe import Mwe
from src.trace.trace import AstContent, PosEncoding, Tracer


def test_tracing_file() -> None:
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
    tracer.trace_mwe()
    assert isinstance(tracer.tracing_result, AstContent)
    assert len(tracer.tracing_result.tatics) == 17

    # Check tactics
    code = code.encode("utf-8")
    tactic = tracer.tracing_result.tatics[0]
    tatic_code = (code[tactic.pos : tactic.end_pos]).decode("utf-8")
    assert tatic_code == "have : 2 < minFac n := h.1.trans_le h.2.2"

    # Check premises
    premise = tracer.tracing_result.premises[-1]
    assert premise.mod_name == "Main"
    assert premise.full_name == "Mathlib.Meta.NormNum.minFacHelper_0"
    logger.info(f"premise: {premise.pos.line}")
    assert premise.pos == PosEncoding(line=35, column=8)
    assert premise.end_pos == PosEncoding(line=35, column=22)
    assert premise.def_pos is None
