from src.logger_config import logger
from src.mwe import Mwe


from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("./tests/data/gym_crashing.lean")
    # produces the following crash error:
    # Main.lean:572:2: error: unknown constant 'Mathlib.Tactic.Ring.zero_pow.match_1'
    mwe = Mwe(
        code,
        "zero_pow",
    )
    mwe.rewrite_to_tactic_style()

    tracer_of_mwe = Tracer(mwe)
    tracer_of_mwe.trace_mwe()
    tactics = tracer_of_mwe.get_traced_tactic(tracer_of_mwe.tracing_result.tatics)
    code = mwe.code.encode("utf-8")

    tatic_codes = list(
        map(lambda tactic: (code[tactic.pos : tactic.end_pos]).decode("utf-8"), tactics)
    )
    logger.debug(f"tactics: {tatic_codes}")

    # Check tactics in gym
    with Gym(mwe) as (gym, state):
        # run in gym
        state_1 = gym.run_tacs(
            state,
            [tactic.get_syntax_of_tactic(code) for tactic in tactics],
        )
        assert isinstance(state_1, ProofFinished)
