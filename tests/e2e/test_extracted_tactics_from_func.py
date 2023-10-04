from loguru import logger

from src.mwe import Mwe
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("../data/Mathlib.Data.Set.Finite.lean")

    mwe = Mwe(
        code,
        "finite_def",
    )
    mwe.rewrite_to_tactic_style()

    tracer = Tracer(mwe)
    tracer.trace_mwe()
    # Get tactics
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)

    code = mwe.code.encode("utf-8")

    tatic_codes = list(
        map(lambda tactic: (code[tactic.pos : tactic.end_pos]).decode("utf-8"), tactics)
    )
    logger.info(f"tactics: {tatic_codes}")
    assert len(tactics) == 1

    # Check tactics in gym
    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tacs(
            state_0,
            [tactic.get_syntax_of_tactic(code) for tactic in tactics],
        )
        assert isinstance(state_1, ProofFinished)
