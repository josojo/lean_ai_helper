# before running this script, one should run the rewriting_in_tactic_style.py script to generate the file with the tactic style code


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
    # trace only once the first theorem to save the updated tracing data
    mwe = Mwe(
        code,
        theorem_names[0],
    )
    tracer = Tracer(mwe)
    # tracer.trace_mwe()

    tactic_counter = 0
    success = 0
    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        # if theorem_name != "image_coe_closedBall":
        #     continue
        mwe = Mwe(
            code,
            theorem_name,
        )

        tracer = Tracer(mwe)
        tracer.load_trace_result(tracing_res_path)
        # Get tactics
        tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
        logger.debug(f"number of tactics: len({len(tactics)})")
        tactics.sort(key=lambda x: x.pos)

        tactic_terms = list(
            map(lambda x: (code_bytes[x.pos : x.end_pos]).decode("utf-8"), tactics)
        )
        logger.debug(f"tactics: {tactic_terms}")
        finishing_tactics = [
            tactic for tactic in tactics if tactic.is_tactic_finishing_proof()
        ]
        logger.debug(f"number of finishing tactics: {len(finishing_tactics)}")

        for tactic in finishing_tactics:
            tactic_counter += 1
            # Check tactics in gym
            with Gym(mwe) as (gym, state_0):
                cmds = [
                    pre_tactic.get_syntax_of_tactic(code_bytes)
                    for pre_tactic in tactics
                    if pre_tactic.end_pos < tactic.pos
                ]
                cmds.append(tactic.get_syntax_of_tactic(code_bytes))
                logger.debug(f"cmds: {cmds}")
                state_1 = gym.run_tacs(
                    state_0,
                    cmds,
                )
                if isinstance(state_1, ProofFinished):
                    success += 1
                else:
                    logger.debug(
                        f"theorem: {theorem_name} did not execute the following tactic:{(code_bytes[tactic.pos : tactic.end_pos]).decode('utf-8')}"
                    )
                    logger.debug(f"failed: {state_1}")
                    logger.debug(f" expected previous state: {tactic.state_before}")
                    logger.debug(f" expected next state: {tactic.state_after}")
                    break
        if success < tactic_counter:
            logger.info(f"out of {tactic_counter} theorems, {success} succeeded")
            break

    logger.info(f"out of {tactic_counter} theorems, {success} succeeded")


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(
        script_dir,
        "../tests/data/Mathlib.Analysis.Complex.UpperHalfPlane.Metric_rewrite.lean",
    )
    # tracing_result_path = os.path.join(
    #     script_dir, "../tests/data/tracing_results/Algebra.Basics.Main.ast.json"
    # )
    tracing_result_path = os.path.join(
        script_dir, "../execution_env/build/ir/Main.ast.json"
    )
    evaluate_all_tactics_of_file_in_gym(file_path, tracing_result_path)
