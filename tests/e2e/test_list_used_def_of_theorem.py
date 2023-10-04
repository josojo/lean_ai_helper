import os

from loguru import logger

from src.trace.trace import Tracer
from tests.utils.utils import initiate_mwe_for_min_fac_helper


def test_list_used_def_of_theorem() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    script_dir = os.path.dirname(os.path.realpath(__file__))

    mwe = initiate_mwe_for_min_fac_helper()

    tracer = Tracer(mwe)
    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Main.ast.json")
    )

    premises = tracer.get_defintions_used_in_theorem()
    logger.info(f"used premises: {list(map(lambda x: x.full_name, premises))}")

    assert list(map(lambda x: x.full_name, premises)) == [
        "Nat",
        "Nat.ble",
        "Bool.true",
        "Mathlib.Meta.NormNum.MinFacHelper",
        "Mathlib.Meta.NormNum.minFacHelper_0",
    ]
    premises = [p for p in premises if p.mod_name == "Main"]
    # Check whether premises are indeed defintions.
    assert list(map(lambda x: x.full_name, premises)) == [
        "Mathlib.Meta.NormNum.MinFacHelper",
        "Mathlib.Meta.NormNum.minFacHelper_0",
    ]
