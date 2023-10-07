from loguru import logger
from src.mwe import Mwe
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    for i in range(0, 2):
        logger.debug(f"i: {i}")
        code = read_code_from_file(
            "./tests/data/Mathlib.Order.Bounds.Basics_rewrite.lean"
        )

        mwe = Mwe(code, "mem_lowerBounds_image", i)

        tracer = Tracer(mwe)
        if i == 0:
            tracer.trace_mwe()
        else:
            tracer.load_trace_result(
                tracer.execution_env.tmp_dir / "build/ir/Main.ast.json"
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
