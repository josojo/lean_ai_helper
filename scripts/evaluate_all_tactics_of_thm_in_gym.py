import os
import re

from typing import List
from pathlib import Path
from loguru import logger

from src.interaction.utils import get_theorem_names_from_code
from src.mwe import Mwe
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished


def evaluate_all_tactics_of_file_in_gym(
    file_with_code_path: Path, tracing_res_path: Path
) -> None:
    code = ""

    # Open the file using the absolute path
    file = open(file_with_code_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    code_bytes = code.encode("utf-8")
    theorem_names = get_theorem_names_from_code(code)
    success = 0
    checkable_theorems = 0
    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        if theorem_name != "algebra_ext":
            continue
        mwe = Mwe(
            code,
            theorem_name,
        )
        tracer = Tracer(mwe)
        tracer.load_trace_result(tracing_res_path)
        # Get tactics
        tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
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
                    f"theorem: {theorem_name} did not execute the following tactic:{[(code_bytes[tactic.pos : tactic.end_pos]).decode('utf-8') for tactic in tactics]}"
                )
                logger.debug(f"failed: {state_1}")
    logger.info(f"out of {checkable_theorems} theorems, {success} succeeded")


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(
        script_dir, "../tests/data/Mathlib.Algebra.Algebra.Basic.lean"
    )
    tracing_result_path = os.path.join(
        script_dir, "../tests/data/tracing_results/Algebra.Basics.Main.ast.json"
    )
    evaluate_all_tactics_of_file_in_gym(file_path, tracing_result_path)
