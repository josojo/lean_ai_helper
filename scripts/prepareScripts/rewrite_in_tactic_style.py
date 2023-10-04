import os

from pathlib import Path
from loguru import logger
from src.interaction.utils import get_theorem_names_from_code

from src.mwe import Mwe
from tests.utils.utils import read_code_from_file


def rewrite_all_proofs_in_tactic_style(
    file_with_code_path: Path, file_for_writing_result: Path
) -> None:
    code = read_code_from_file(file_with_code_path)

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
        script_dir,
        "../../tests/data/Mathlib.Analysis.Complex.UpperHalfPlane.Metric.lean",
    )
    file_path_new = os.path.join(
        script_dir,
        "../../tests/data/Mathlib.Analysis.Complex.UpperHalfPlane.Metric_rewrite.lean",
    )
    rewrite_all_proofs_in_tactic_style(file_path, file_path_new)
