import pytest
import os

from loguru import logger

from src.mwe import Mwe
from src.trace.trace import Tracer


def test_list_premises_of_tactic() -> None:
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
    tracer.load_trace_result(os.path.join(script_dir, "../data/tracing_results/Main.ast.json"))
    tactic = tracer.tracing_result.tatics[-5]

    premises = tracer.get_premises_from_tactic(tactic)
    code = code.encode("utf-8")
    tatic_code = (code[tactic.pos : tactic.end_pos]).decode("utf-8")
    logger.info(f"tactic: {tatic_code}")
    logger.info(f"used premises: {list(map(lambda x: x.full_name, premises))}")
    assert tatic_code == "rcases hp.eq_or_lt with rfl|h"
    assert list(map(lambda x: x.full_name, premises)) == ["LE.le.eq_or_lt"]
