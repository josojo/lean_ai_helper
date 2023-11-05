from src.mwe import Mwe
from src.utils.reader import read_code_from_file


def initiate_mwe_for_disjoint_to_finset() -> Mwe:
    code = read_code_from_file("./tests/data/Mathlib.Data.Set.Finite.lean")
    mwe = Mwe(
        code,
        "disjoint_toFinset",
    )
    return mwe


def initiate_mwe_for_min_fac_helper() -> Mwe:
    code = read_code_from_file("./tests/data/Mathlib.Meta.NormNum.Prime.lean")
    mwe = Mwe(
        code,
        "minFacHelper_0",
    )
    return mwe


def initiate_mwe_for_finite_def() -> Mwe:
    code = read_code_from_file("./tests/data/Mathlib.Data.Set.Finite.lean")
    mwe = Mwe(
        code,
        "finite_def",
    )
    return mwe

def initiate_mwe_for_rw() -> Mwe:
    code = read_code_from_file("./tests/data/rw.lean")
    mwe = Mwe(
        code,
        "oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two",
    )
    return mwe

def initiate_mwe_for_rw_2() -> Mwe:
    code = read_code_from_file("./tests/data/rw.lean")
    mwe = Mwe(
        code,
        "oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two",
    )
    return mwe