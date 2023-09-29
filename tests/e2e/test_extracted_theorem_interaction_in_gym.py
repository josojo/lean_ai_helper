import pytest
import os

from src.mwe import Mwe
from src.trace.trace import AstContent, Tracer
from src.interaction.gym import Gym, ProofFinished


def test_extracted_theorem_interaction_in_gym() -> None:
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
    ast_content = tracer.trace_mwe()
    assert isinstance(ast_content, AstContent)
    assert len(ast_content.tatics) == 17

    # Get tactics
    code_bytes = code.encode("utf-8")
    tactics = tracer.get_traced_tactic(ast_content.tatics)

    # Check tactics in gym
    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tacs(
            state_0,
            [
                (code_bytes[tactic.pos : tactic.end_pos]).decode("utf-8")
                for tactic in tactics
            ],
        )
        assert isinstance(state_1, ProofFinished)