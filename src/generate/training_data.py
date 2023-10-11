# before running this script, one should run the rewriting_in_tactic_style.py
# script to generate the file with the tactic style code

import os
from pathlib import Path
from typing import List
import json
from filelock import FileLock

import ray

from src.utils.reader import get_objects_for_theorem
from src.utils.lean_code_modifier import (
    rewrite_all_proofs_in_tactic_style,
)
from src.utils.lean_code_modifier import remove_comments_from_lean_file

# from src.logger_config import logger
from src.interaction.utils import get_theorem_names_from_code
from src.mwe import Mwe, UnusualTheoremFormatError
from src.trace.trace import Tracer

from src.utils.reader import read_code_from_file


@ray.remote
def generate_training_data(
    file_with_code_path: Path,
    environment: Path,
    output_file: Path,
) -> None:
    tmp_dir = Path(
        os.path.normpath(
            os.path.join(
                os.path.dirname(os.path.realpath(__file__)), f"../../{environment}/"
            )
        )
    )
    tracing_result_path = Path(os.path.join(tmp_dir, "build/ir/Main.ast.json"))
    code = read_code_from_file(file_with_code_path)

    code_bytes = code.encode("utf-8")
    theorem_names = get_theorem_names_from_code(code)

    if len(theorem_names) == 0:
        return

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
    except UnusualTheoremFormatError:
        return
    lock_path = Path(str(output_file) + ".lock")

    for k, theorem_name in enumerate(theorem_names):
        iteration = 0
        while (
            k - 1 - iteration >= 0 and theorem_name == theorem_names[k - 1 - iteration]
        ):
            iteration += 1
        try:
            mwe, tactics = get_objects_for_theorem(
                theorem_name, code, tracing_result_path, iteration
            )
        except UnusualTheoremFormatError:
            continue
        tactics.sort(key=lambda x: x.pos)
        tracer = Tracer(mwe)
        tracer.load_trace_result(tracing_result_path)
        json_data = {
            "theorem_name": theorem_name,
            "file_path": str(file_with_code_path),
            "tactics": [
                {
                    "syntax": tactic.get_syntax_of_tactic(code_bytes),
                    "premises": list(
                        map(
                            lambda x: x.full_name,
                            tracer.get_premises_from_tactic(tactic),
                        )
                    ),
                }
                for tactic in tactics
            ],
            "defintions": list(
                map(lambda x: x.full_name, tracer.get_defintions_used_in_theorem())
            ),
        }
        with FileLock(lock_path):
            with open(output_file, "a", encoding="utf-8") as file:
                file.write(json.dumps(json_data) + ",\n")
    return


def initate_array_in_output_file(output_file: Path) -> None:
    with open(output_file, "w", encoding="utf-8") as file:
        file.write("[")


def close_array_in_output_file(output_file: Path) -> None:
    with open(output_file, "r+b") as file:  # Open in read+write binary mode
        if file.read(1):  # Check if file is not empty
            file.seek(-2, 2)  # Go to one byte before the end
            file.write(b"]")  # Write the replacement character


def get_all_files_from_dictionary(path: Path) -> List[Path]:
    files_in_path = []
    for root, _, files in os.walk(path):
        for file in files:
            files_in_path.append(Path(os.path.join(root, file)))
    return files_in_path


def prepare_lean_files_by_rewriting_and_removing_comments(
    all_lean_files: List[Path], input_dir: Path, output_dir: Path
) -> None:
    for file in all_lean_files:
        relative_path = os.path.relpath(file, input_dir)
        file_path_new = Path(os.path.join(output_dir, relative_path))
        rewrite_all_proofs_in_tactic_style(file, file_path_new)
        remove_comments_from_lean_file(file_path_new)
