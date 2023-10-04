import os

from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import initiate_mwe_for_min_fac_helper


def test_extracted_theorem_interaction_in_gym() -> None:
    mwe = initiate_mwe_for_min_fac_helper()

    tracer = Tracer(mwe)
    script_dir = os.path.dirname(os.path.realpath(__file__))
    tracer.load_trace_result(
        os.path.join(script_dir, "../data/tracing_results/Main.ast.json")
    )
    # Get tactics
    code_bytes = mwe.code.encode("utf-8")
    tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)

    # Check tactics in gym
    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tacs(
            state_0,
            [tactic.get_syntax_of_tactic(code_bytes) for tactic in tactics],
        )
        assert isinstance(state_1, ProofFinished)
