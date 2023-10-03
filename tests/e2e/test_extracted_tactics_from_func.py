import pytest
import os

from src.mwe import Mwe
from src.trace.trace import AstContent, Tracer
from src.interaction.gym import Gym, ProofFinished
from loguru import logger


def test_extracted_theorem_interaction_in_gym() -> None:
    code = ""
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(script_dir, "../data/Mathlib.Data.Set.Finite.lean")

    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

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
