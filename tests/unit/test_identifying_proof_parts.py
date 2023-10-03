import pytest
import os

from src.mwe import Mwe
from src.trace.trace import AstContent, Tracer
from src.interaction.gym import Gym, ProofFinished
from loguru import logger


def test_extracted_theorem_interaction_in_gym() -> None:
    code = ""
    script_dir = os.path.dirname(os.path.realpath(__file__))

    file_path = os.path.join(script_dir, "../data/Mathlib.Algebra.Algebra.Basic.lean")
    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    mwe = Mwe(
        code,
        "algebra_ext",
    )
    assert (
        mwe.code[mwe.theorem_start : mwe.proof_start]
        == "theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)\n    (h : ∀ r : R, (haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :\n    P = Q :="
    )
