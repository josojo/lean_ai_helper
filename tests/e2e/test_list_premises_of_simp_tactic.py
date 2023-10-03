import os

from loguru import logger

from src.mwe import Mwe
from src.trace.trace import Tracer


def test_list_premises_of_tactic() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""

    code = ""
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(script_dir, "../data/Mathlib.Algebra.Algebra.Basic.lean")

    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    mwe = Mwe(
        code,
        "mul_sub_algebraMap_pow_commutes",
    )
    tracer = Tracer(mwe)
    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Algebra.Basics.Main.ast.json")
    )
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
    logger.info(f"tactics: {tactics}")
    tactic = tactics[-2]
    premises = tracer.get_premises_from_tactic(tactic)
    code = code.encode("utf-8")
    tatic_code = (code[tactic.pos : tactic.end_pos]).decode("utf-8")
    assert tatic_code == "· simp"
    assert len(premises) == 0
