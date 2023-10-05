import os

from src.logger_config import logger

from src.mwe import Mwe
from src.trace.trace import Tracer
from tests.utils.utils import read_code_from_file


def test_list_premises_of_tactic() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = read_code_from_file("./tests/data/Mathlib.Algebra.Algebra.Basic.lean")
    script_dir = os.path.dirname(os.path.realpath(__file__))

    mwe = Mwe(
        code,
        "mul_sub_algebraMap_pow_commutes",
    )
    tracer = Tracer(mwe)
    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Algebra.Basics.Main.ast.json")
    )
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
    logger.debug(f"tactics: {tactics}")
    tactic = tactics[-2]
    premises = tracer.get_premises_from_tactic(tactic)
    code = code.encode("utf-8")
    tatic_code = tactic.get_syntax_of_tactic(code)
    assert tatic_code == "  · simp"
    assert len(premises) == 0
