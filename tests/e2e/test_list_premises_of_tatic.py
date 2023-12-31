import os

from src.logger_config import logger

from src.mwe import Mwe
from src.trace.trace import Tracer
from tests.utils.utils import read_code_from_file


def test_list_premises_of_tactic() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = read_code_from_file("./tests/data/Mathlib.Meta.NormNum.Prime.lean")
    script_dir = os.path.dirname(os.path.realpath(__file__))

    mwe = Mwe(
        code,
        "minFacHelper_0",
    )
    tracer = Tracer(mwe)
    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Main.ast.json")
    )
    tactic = tracer.tracing_result.tatics[-5]

    premises = tracer.get_premises_from_tactic(tactic)
    code = code.encode("utf-8")
    tatic_code = tactic.get_syntax_of_tactic(code)
    logger.debug(f"tactic: {tatic_code}")
    logger.debug(f"used premises: {list(map(lambda x: x.full_name, premises))}")
    assert tatic_code == "    rcases hp.eq_or_lt with rfl|h"
    assert list(map(lambda x: x.full_name, premises)) == ["LE.le.eq_or_lt"]
