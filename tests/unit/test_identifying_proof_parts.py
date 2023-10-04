from src.mwe import Mwe
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("../data/Mathlib.Algebra.Algebra.Basic.lean")
    mwe = Mwe(
        code,
        "algebra_ext",
    )
    assert (
        mwe.code[mwe.theorem_start : mwe.proof_start]
        == "theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} \
[Semiring A] (P Q : Algebra R A)\n    (h : ∀ r : R, \
(haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :\n    P = Q :="
    )
