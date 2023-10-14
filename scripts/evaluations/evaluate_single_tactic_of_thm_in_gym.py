# before running this script, one should run the rewriting_in_tactic_style.py
# script to generate the file with the tactic style code

import os
import sys
from ast import Tuple
from pathlib import Path
from typing import Optional

import ray
from src.generate.training_data import (
    get_all_files_from_dictionary,
    prepare_lean_files_by_rewriting_and_removing_comments,
)
from src.lean_env.setup import ParallelExecutor

from src.utils.reader import get_objects_for_theorem

from src.logger_config import logger
from src.interaction.utils import get_theorem_names_from_code
from src.mwe import Mwe, UnusualTheoremFormatError
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished
from src.utils.utils import get_folder_and_path_from_path

from tests.utils.utils import read_code_from_file


@ray.remote
def evaluate_final_tactics_of_file_in_gym(
    file_with_code_path: Path,
    environment: Path,
    _output_file: Optional[Path] = None,
) -> Tuple(int, int):
    tmp_dir = Path(
        os.path.normpath(
            os.path.join(
                os.path.dirname(os.path.realpath(__file__)), f"../../{environment}/"
            )
        )
    )
    tracing_result_path = os.path.join(tmp_dir, "build/ir/Main.ast.json")
    logger.debug("Testing with file: " + str(file_with_code_path))
    code = read_code_from_file(file_with_code_path)

    code_bytes = code.encode("utf-8")
    theorem_names = get_theorem_names_from_code(code)

    if len(theorem_names) == 0:
        logger.debug(f"file: {file_with_code_path} has no theorems")
        return 0, 0

    ## We sort theorem names in order to deal with the theorems
    # with the same name one after the other
    theorem_names.sort()

    # trace only once the first theorem to save the updated tracing data
    try:
        Tracer(
            Mwe(
                code,
                theorem_names[0],
            ),
            tmp_dir,
        ).trace_mwe()
    except UnusualTheoremFormatError as err:
        logger.debug(f"failed to get objects for theorem: {theorem_names[0]}")
        logger.debug(err)
        return 0, 0

    tactic_counter = 0
    success = 0
    for k, theorem_name in enumerate(theorem_names):
        logger.debug(f"Testing with theorem: {theorem_name}")
        # if theorem_name != "image_coe_closedBall":
        #     continue
        iteration = 0
        while (
            k - 1 - iteration >= 0 and theorem_name == theorem_names[k - 1 - iteration]
        ):
            iteration += 1
        try:
            mwe, tactics = get_objects_for_theorem(
                theorem_name, code, tracing_result_path, iteration
            )
        except UnusualTheoremFormatError as err:
            logger.debug(f"failed to get objects for theorem: {theorem_name}")
            logger.debug(err)
            continue
        logger.debug(f"number of tactics: len({len(tactics)})")
        tactics.sort(key=lambda x: x.pos)

        finishing_tactics = [
            tactic for tactic in tactics if tactic.is_tactic_finishing_proof()
        ]
        logger.debug(f"number of finishing tactics: {len(finishing_tactics)}")

        for tactic in finishing_tactics:
            tactic_counter += 1
            # Check tactics in gym
            with Gym(mwe, None, tmp_dir) as (gym, state_0):
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
                    logger.info(f"for the file: {file_with_code_path}")
                    logger.info(
                        f"theorem: {theorem_name} did not execute the following \
                            tactic:{(code_bytes[tactic.pos : tactic.end_pos]).decode('utf-8')}"
                    )
                    logger.info(f"failed: {state_1}")
                    logger.debug(f" expected previous state: {tactic.state_before}")
                    logger.debug(f" expected next state: {tactic.state_after}")
                    break

    logger.info(f"out of {tactic_counter} theorems, {success} succeeded")
    return success, tactic_counter


if __name__ == "__main__":
    # Config parameters
    NUM_CPUS = 4
    path_to_mathlib4 = Path(sys.argv[1])

    # Init parallel execution environment
    executor = ParallelExecutor(NUM_CPUS)

    # Get all files in mathlib
    all_files_in_path = get_all_files_from_dictionary(path_to_mathlib4)

    # Rewrite all proofs in tactic style and remove comments
    path, foldername = get_folder_and_path_from_path(path_to_mathlib4)

    path_to_mathlib4_new = os.path.join(path, str(foldername) + "_rewritten")
    prepare_lean_files_by_rewriting_and_removing_comments(
        all_files_in_path, path_to_mathlib4, path_to_mathlib4_new
    )
    all_files_in_path = get_all_files_from_dictionary(path_to_mathlib4_new)

    # strip down the number of files to investigate for faster execution
    all_files_in_path = all_files_in_path[210:]
    results = executor.run(evaluate_final_tactics_of_file_in_gym, all_files_in_path)
    SUCCESS_CNT = 0
    EXECUTION_CNT = 0
    for result in results:
        i, j = result
        SUCCESS_CNT += i
        EXECUTION_CNT += j
        print(result)
    logger.info(f"out of {EXECUTION_CNT} theorems, {SUCCESS_CNT} succeeded")
    ray.shutdown()
