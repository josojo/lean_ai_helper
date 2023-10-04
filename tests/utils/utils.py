import os

from pathlib import Path

from src.mwe import Mwe


def initiate_mwe_for_disjoint_to_finset() -> Mwe:
    code = read_code_from_file("../data/Mathlib.Data.Set.Finite.lean")
    mwe = Mwe(
        code,
        "disjoint_toFinset",
    )
    return mwe


def initiate_mwe_for_min_fac_helper() -> Mwe:
    code = read_code_from_file("../data/Mathlib.Meta.NormNum.Prime.lean")
    mwe = Mwe(
        code,
        "minFacHelper_0",
    )
    return mwe


def initiate_mwe_for_finite_def() -> Mwe:
    code = read_code_from_file("../data/Mathlib.Data.Set.Finite.lean")
    mwe = Mwe(
        code,
        "finite_def",
    )
    return mwe


def read_code_from_file(data_path: Path) -> str:
    code = ""
    # Get the absolute path to the directory of the current script
    script_dir = os.path.dirname(os.path.realpath(__file__))

    # Join the script directory with the relative path to the file
    file_path = os.path.join(script_dir, data_path)

    # Open the file using the absolute path
    with open(file_path, "r", encoding="utf-8") as file:
        code = file.read()

    return code
