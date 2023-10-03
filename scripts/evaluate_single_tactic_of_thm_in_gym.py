import os
import re

from typing import List
from pathlib import Path
from loguru import logger

from src.mwe import Mwe
from src.trace.trace import Tracer
from src.interaction.gym import Gym, ProofFinished


def get_theorem_names_from_code(code: str) -> List[str]:
    theorem_names = []
    lines = code.split("\n")
    for line in lines:
        match = re.search(r"\btheorem\b\s+(\w+)", line)
        if match:
            theorem_names.append(match.group(1))
    return theorem_names


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

    tactic_counter = 0
    success = 0
    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        mwe = Mwe(
            code,
            theorem_name,
        )
        tracer = Tracer(mwe)
        tracer.load_trace_result(tracing_res_path)
        # Get tactics
        tactics = tracer.get_traced_tactic(tracer.tracing_result.tatics)
        tactics.sort(key=lambda x: x.pos)
        finishing_tactics = [
            tactic for tactic in tactics if tactic.is_tactic_finishing_proof()
        ]

        for tactic in finishing_tactics:
            logger.debug(
                "testing tactic"
                + (code_bytes[tactic.pos : tactic.end_pos]).decode("utf-8")
            )
            tactic_counter += 1
            # Check tactics in gym
            with Gym(mwe) as (gym, state_0):
                cmds = [
                    (code_bytes[pre_tactic.pos : pre_tactic.end_pos]).decode("utf-8")
                    for pre_tactic in tactics
                    if pre_tactic.end_pos < tactic.pos
                ]
                cmds.append((code_bytes[tactic.pos : tactic.end_pos]).decode("utf-8"))
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
        script_dir, "../tests/data/Mathlib.Algebra.Algebra.Basic.lean"
    )
    tracing_result_path = os.path.join(
        script_dir, "../tests/data/tracing_results/Algebra.Basics.Main.ast.json"
    )
    evaluate_all_tactics_of_file_in_gym(file_path, tracing_result_path)
