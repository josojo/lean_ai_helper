from src.mwe import Mwe
from src.utils.reader import read_code_from_file


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
