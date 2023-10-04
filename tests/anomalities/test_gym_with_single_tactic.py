import os
from loguru import logger

from src.interaction.gym import Gym, ProofFinished
from src.mwe import Mwe
from src.trace.trace import Tracer
from tests.utils.utils import read_code_from_file


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = read_code_from_file("../data/Mathlib.Algebra.Algebra.Basic.lean")
    script_dir = os.path.dirname(os.path.realpath(__file__))
    mwe = Mwe(
        code,
        "algebra_ext",
    )
    tracer = Tracer(mwe)

    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Algebra.Basics.Main.ast.json")
    )
    # Get tactics
    code_bytes = code.encode("utf-8")
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)

    # Check tactics in gym
    tactic = tactics[-1]
    logger.info(f"tactic: {tactic.get_syntax_of_tactic(code_bytes)}")

    # For some reason the following does not work:
    # But running all tactics one by one works:
    # {"sid": 0, "cmd": ["replace h : P.toRingHom = Q.toRingHom := FunLike.ext _ _ h",
    # "have h' : (haveI := P; (\u00b7 \u2022 \u00b7) : R \u2192 A \u2192 A) =
    # (haveI := Q; (\u00b7 \u2022 \u00b7) : R \u2192 A \u2192 A) :=
    # by\n    funext r a\n    rw [P.smul_def', Q.smul_def', h]",
    # "rcases P with @\u27e8\u27e8P\u27e9\u27e9",
    # "rcases Q with @\u27e8\u27e8Q\u27e9\u27e9"]}
    # {"sid":0, "cmd":["  congr"]}
    with Gym(mwe, tactic) as (gym, state_0):
        state_1 = gym.run_tacs(state_0, [tactic.get_syntax_of_tactic(code_bytes)])
        logger.debug(f"state_1: {state_1}")
        assert not isinstance(state_1, ProofFinished)
