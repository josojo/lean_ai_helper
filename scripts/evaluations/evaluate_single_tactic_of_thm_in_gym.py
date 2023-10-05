# before running this script, one should run the rewriting_in_tactic_style.py
# script to generate the file with the tactic style code

import os
from ast import Tuple
from pathlib import Path
from collections import deque

import ray

from scripts.helpers.helpers import get_objects_for_theorem
from src.utils.lean_code_modifier import (
    rewrite_all_proofs_in_tactic_style,
)
from src.utils.lean_code_modifier import remove_comments_from_lean_file

from src.logger_config import logger
from src.interaction.utils import get_theorem_names_from_code
from src.mwe import Mwe, UnusualTheoremFormatError
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished

from tests.utils.utils import read_code_from_file


@ray.remote
def evaluate_all_tactics_of_file_in_gym(
    file_with_code_path: Path,
    tracing_res_path: Path,
    with_tracing: bool,
    temp_dir: Path,
) -> Tuple(int, int):
    code = read_code_from_file(file_with_code_path)

    code_bytes = code.encode("utf-8")
    theorem_names = get_theorem_names_from_code(code)

    if len(theorem_names) == 0:
        logger.debug(f"file: {file_with_code_path} has no theorems")
        return 0, 0
    # trace only once the first theorem to save the updated tracing data
    if with_tracing:
        try:
            Tracer(
                Mwe(
                    code,
                    theorem_names[0],
                ),
                temp_dir,
            ).trace_mwe()
        except UnusualTheoremFormatError as err:
            logger.debug(f"failed to get objects for theorem: {theorem_names[0]}")
            logger.debug(err)
            return 0, 0

    tactic_counter = 0
    success = 0
    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        # if theorem_name != "image_coe_closedBall":
        #     continue
        try:
            mwe, tactics = get_objects_for_theorem(theorem_name, code, tracing_res_path)
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
            with Gym(mwe, None, temp_dir) as (gym, state_0):
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
        # if success < tactic_counter:
        #     logger.info(f"out of {tactic_counter} theorems, {success} succeeded")
        #     break

    logger.info(f"out of {tactic_counter} theorems, {success} succeeded")
    return success, tactic_counter


if __name__ == "__main__":
    NUM_CPUS = 2
    ray.init(num_cpus=NUM_CPUS)
    execution_envs = [f"execution_env_{i}" for i in range(NUM_CPUS)]
    for folder in execution_envs:
        os.makedirs(folder, exist_ok=True)
    # Create a queue for folders
    execution_envs_queue = deque(execution_envs)

    results = []
    futures = {}
    path_to_mathlib4 = Path("/Users/josojo/coding/ai/lean/mathlib4/Mathlib/")
    all_files_in_path = []
    for root, dirs, files in os.walk(path_to_mathlib4):
        for file in files:
            all_files_in_path.append(os.path.join(root, file))
    for file in all_files_in_path:
        file_path_new = file.replace("mathlib4", "mathlib4_new")
        rewrite_all_proofs_in_tactic_style(file, file_path_new)
        remove_comments_from_lean_file(file_path_new)

    files_to_investigate = []
    path_to_mathlib4_new = Path("/Users/josojo/coding/ai/lean/mathlib4_new/Mathlib/")
    for root, dirs, files in os.walk(path_to_mathlib4_new):
        for file in files:
            files_to_investigate.append(os.path.join(root, file))

    files_to_investigate = files_to_investigate[214:215]
    #     "../tests/data/Mathlib.AlgebraicTopology.SimplexCategory_rewrite.lean",
    #     "../tests/data/Mathlib.Analysis.Complex.UpperHalfPlane.Metric_rewrite.lean",
    #     "../tests/data/Mathlib.Algebra.Algebra.Basic_rewrite.lean",
    # ]
    script_dir = os.path.dirname(os.path.realpath(__file__))

    for file_path in files_to_investigate:
        file_path = os.path.join(
            script_dir,
            file_path,
        )
        # Wait for an available folder
        while not execution_envs_queue:
            # Check for completed tasks
            ready_ids, remaining_ids = ray.wait(
                list(futures.keys()), num_returns=1, timeout=0
            )

            for done_id in ready_ids:
                # Retrieve the result, free up the folder, and remove from tracking dict
                result = ray.get(done_id)
                results.append(result)
                i, j = result
                # if i < j:
                #     raise ValueError("found unsuccessful tactic")
                execution_envs_queue.append(futures.pop(done_id))

        # Start a task with an available folder
        env = execution_envs_queue.popleft()
        tmp_dir = Path(os.path.normpath(os.path.join(script_dir, f"../{env}/")))
        tracing_result_path = os.path.join(tmp_dir, "build/ir/Main.ast.json")
        logger.debug("Testing with file: " + file_path)
        future = evaluate_all_tactics_of_file_in_gym.remote(
            file_path, tracing_result_path, True, tmp_dir
        )
        futures[future] = env

    # Wait for all remaining tasks to finish
    results.extend(ray.get(list(futures.keys())))
    SUCCESS_CNT = 0
    EXECUTION_CNT = 0
    for result in results:
        i, j = result
        SUCCESS_CNT += i
        EXECUTION_CNT += j
        print(result)
    logger.info(f"out of {EXECUTION_CNT} theorems, {SUCCESS_CNT} succeeded")
    ray.shutdown()
