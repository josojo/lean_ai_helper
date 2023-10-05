from src.mwe import Mwe
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("../data/anomalie.2_rewrite.lean")

    mwe = Mwe(
        code,
        "exists_not_acc_lt_of_not_acc",
    )

    tracer = Tracer(mwe)
    tracer.trace_mwe()
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
