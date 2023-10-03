import os
import re

from typing import List
from pathlib import Path
from loguru import logger

from src.mwe import Mwe


def get_theorem_names_from_code(code: str) -> List[str]:
    theorem_names = []
    lines = code.split("\n")
    for line in lines:
        match = re.search(r"\btheorem\b\s+(\w+)", line)
        if match:
            theorem_names.append(match.group(1))
    return theorem_names


def rewrite_all_proofs_in_tactic_style(
    file_with_code_path: Path, file_for_writing_result: Path
) -> None:
    code = ""

    file = open(file_with_code_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    theorem_names = get_theorem_names_from_code(code)

    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        mwe = Mwe(
            code,
            theorem_name,
        )
        mwe.rewrite_to_tactic_style()
        code = mwe.code

    # Write the newly generated code back into the file
    with open(file_for_writing_result, "w", encoding="utf-8") as file:
        file.write(code)


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(
        script_dir, "../../tests/data/Mathlib.Algebra.Algebra.Basic.lean"
    )
    file_path_new = os.path.join(
        script_dir, "../../tests/data/Mathlib.Algebra.Algebra.Basic_rewrite.lean"
    )
    rewrite_all_proofs_in_tactic_style(file_path, file_path_new)
