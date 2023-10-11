import os

from pathlib import Path
from src.utils.reader import get_objects_for_theorem

from src.logger_config import logger
from src.interaction.utils import get_theorem_names_from_code
from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import read_code_from_file


def evaluate_all_tactics_of_file_in_gym(
    file_with_code_path: Path, tracing_res_path: Path
) -> None:
    code = read_code_from_file(file_with_code_path)

    code_bytes = code.encode("utf-8")
    theorem_names = get_theorem_names_from_code(code)
    success = 0
    checkable_theorems = 0
    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        if theorem_name != "algebra_ext":
            continue
        mwe, tactics = get_objects_for_theorem(theorem_name, code, tracing_res_path)
        if not tactics:
            logger.debug(f"theorem: {theorem_name} has no tactics")
            continue
        checkable_theorems += 1
        # Check tactics in gym
        with Gym(mwe) as (gym, state_0):
            state_1 = gym.run_tacs(
                state_0,
                [
                    (code_bytes[tactic.pos : tactic.end_pos]).decode("utf-8")
                    for tactic in tactics
                ],
            )
            if isinstance(state_1, ProofFinished):
                success += 1
            else:
                logger.debug(
                    f"theorem: {theorem_name} did not execute the following tactic:\
                {[(code_bytes[tactic.pos : tactic.end_pos]).decode('utf-8') for tactic in tactics]}"
                )
                logger.debug(f"failed: {state_1}")
    logger.info(f"out of {checkable_theorems} theorems, {success} succeeded")


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(
        script_dir, "../../tests/data/Mathlib.Algebra.Algebra.Basic.lean"
    )
    tracing_result_path = os.path.join(
        script_dir, "../../tests/data/tracing_results/Algebra.Basics.Main.ast.json"
    )
    evaluate_all_tactics_of_file_in_gym(file_path, tracing_result_path)
