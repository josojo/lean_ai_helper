from pathlib import Path
import os
import sys

from src.generate.training_data import (
    generate_training_data,
    get_all_files_from_dictionary,
    initate_array_in_output_file,
    prepare_lean_files_by_rewriting_and_removing_comments,
    close_array_in_output_file,
)
from src.lean_env.setup import ParallelExecutor
from src.utils.utils import remove_last_slash


if __name__ == "__main__":

    # Config parameters
    path_to_mathlib4 = Path(sys.argv[1])
    path_to_mathlib4_new = Path(remove_last_slash(sys.argv[1]) + "_rewritten")
    NUM_CPUS = 2

    # Init parallel execution environment
    executor = ParallelExecutor(NUM_CPUS)

    # Get all files in mathlib
    all_files_in_path = get_all_files_from_dictionary(path_to_mathlib4)

    # Rewrite all proofs in tactic style and remove comments
    prepare_lean_files_by_rewriting_and_removing_comments(
        all_files_in_path, path_to_mathlib4, path_to_mathlib4_new
    )
    all_files_in_path = get_all_files_from_dictionary(path_to_mathlib4_new)

    # strip down the number of files to investigate for faster execution
    all_files_in_path = all_files_in_path[0:10]
    script_dir = os.path.dirname(os.path.realpath(__file__))
    output_file = os.path.join(
        script_dir,
        "../../output.json",
    )
    initate_array_in_output_file(output_file)
    results = executor.run(generate_training_data, all_files_in_path)
    close_array_in_output_file(output_file)
