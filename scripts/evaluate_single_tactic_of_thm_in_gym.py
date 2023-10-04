# before running this script, one should run the rewriting_in_tactic_style.py
# script to generate the file with the tactic style code

import os
from ast import Tuple
from pathlib import Path
from collections import deque
from loguru import logger

import ray

from scripts.helpers.helpers import get_objects_for_theorem
from src.interaction.utils import get_theorem_names_from_code

from src.mwe import Mwe
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
    # trace only once the first theorem to save the updated tracing data
    if with_tracing:
        Tracer(
            Mwe(
                code,
                theorem_names[0],
            ),
            temp_dir,
        ).trace_mwe()

    tactic_counter = 0
    success = 0
    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        # if theorem_name != "image_coe_closedBall":
        #     continue
        mwe, tactics = get_objects_for_theorem(theorem_name, code, tracing_res_path)
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
                    logger.debug(
                        f"theorem: {theorem_name} did not execute the following \
                            tactic:{(code_bytes[tactic.pos : tactic.end_pos]).decode('utf-8')}"
                    )
                    logger.debug(f"failed: {state_1}")
                    logger.debug(f" expected previous state: {tactic.state_before}")
                    logger.debug(f" expected next state: {tactic.state_after}")
                    break
        if success < tactic_counter:
            logger.info(f"out of {tactic_counter} theorems, {success} succeeded")
            break

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
    files_to_investigate = [
        "../tests/data/Mathlib.AlgebraicTopology.SimplexCategory_rewrite.lean",
        "../tests/data/Mathlib.Analysis.Complex.UpperHalfPlane.Metric_rewrite.lean",
        "../tests/data/Mathlib.Algebra.Algebra.Basic_rewrite.lean",
    ]
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
                results.append(ray.get(done_id))
                execution_envs_queue.append(futures.pop(done_id))

        # Start a task with an available folder
        env = execution_envs_queue.popleft()
        tmp_dir = Path(os.path.normpath(os.path.join(script_dir, f"../{env}/")))
        tracing_result_path = os.path.join(tmp_dir, "build/ir/Main.ast.json")
        future = evaluate_all_tactics_of_file_in_gym.remote(
            file_path, tracing_result_path, True, tmp_dir
        )
        futures[future] = env

    # Wait for all remaining tasks to finish
    results.extend(ray.get(list(futures.keys())))
    for result in results:
        print(result)
    ray.shutdown()
