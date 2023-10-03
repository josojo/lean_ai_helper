import pytest
import os
from loguru import logger

from src.interaction.gym import Gym, ProofFinished
from src.mwe import Mwe
from src.trace.trace import Tracer


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = ""
    # Get the absolute path to the directory of the current script
    script_dir = os.path.dirname(os.path.realpath(__file__))

    # Join the script directory with the relative path to the file
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

    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Main.ast.json")
    )
    # Get tactics
    code_bytes = code.encode("utf-8")
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)

    # Check tactics in gym
    tactic = tactics[-1]
    logger.info(
        f"tactic: {[(code_bytes[tactic.pos : tactic.end_pos]).decode('utf-8')]}"
    )
    with Gym(mwe, tactic) as (gym, state_0):
        state_1 = gym.run_tacs(
            state_0, [(code_bytes[tactic.pos : tactic.end_pos]).decode("utf-8")]
        )
        assert isinstance(state_1, ProofFinished)

    tactic = tactics[-2]
    with Gym(mwe, tactic) as (gym, state_0):
        state_1 = gym.run_tacs(
            state_0,
            [tactic.get_syntax_of_tactic(code_bytes)],
        )
        assert state_1.message == ""
