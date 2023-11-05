import os

from pathlib import Path

from src.logger_config import logger
from src.interaction.utils import get_theorem_names_from_code
from src.mwe import Mwe, UnusualTheoremFormatError
from src.utils.reader import read_code_from_file


def remove_comments_from_lean_file(filename: Path) -> None:
    with open(filename, "r", encoding="utf-8") as file:
        lines = file.readlines()

    is_comment = False
    with open(filename, "w", encoding="utf-8") as file:
        for line in lines:
            stripped_line = line.lstrip()
            if stripped_line.startswith("/--"):
                is_comment = True
            if not stripped_line.startswith("--") and not is_comment:
                file.write(line)
            if is_comment and stripped_line.find("-/") != -1:
                is_comment = False


def rewrite_all_proofs(
    file_with_code_path: Path, file_for_writing_result: Path
) -> None:
    logger.debug(f"Testing with file: {file_with_code_path}")
    code = read_code_from_file(file_with_code_path)

    theorem_names = get_theorem_names_from_code(code)

    for theorem_name in theorem_names:
        logger.debug(f"Testing with theorem: {theorem_name}")
        try:
            mwe = Mwe(
                code,
                theorem_name,
            )
            mwe.rewrite_to_tactic_style()
            mwe.rewrite_expand_rw()
            code = mwe.code
        except UnusualTheoremFormatError as err:
            logger.debug(f"failed to get objects for theorem: {theorem_name}")
            logger.debug(err)
            continue

    # Create all necessary folders to access the path of file_for_writing_result
    os.makedirs(os.path.dirname(file_for_writing_result), exist_ok=True)
    # Write the newly generated code back into the file
    with open(file_for_writing_result, "w", encoding="utf-8") as file:
        file.write(code)