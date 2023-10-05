import os
from src.logger_config import logger

from src.interaction.gym import Gym, ProofFinished
from src.trace.trace import Tracer
from tests.utils.utils import initiate_mwe_for_min_fac_helper


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    mwe = initiate_mwe_for_min_fac_helper()
    script_dir = os.path.dirname(os.path.realpath(__file__))
    tracer = Tracer(mwe)

    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Main.ast.json")
    )
    # Get tactics
    code_bytes = mwe.code.encode("utf-8")
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)

    # Check tactics in gym
    tactic = tactics[-1]
    logger.debug(
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
