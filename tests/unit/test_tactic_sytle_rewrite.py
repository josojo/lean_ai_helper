import pytest
import os

from src.mwe import Mwe
from src.trace.trace import AstContent, Tracer
from src.interaction.gym import Gym, ProofFinished
from loguru import logger


def test_extracted_theorem_interaction_in_gym() -> None:
    code = ""
    script_dir = os.path.dirname(os.path.realpath(__file__))
    file_path = os.path.join(script_dir, "../data/Mathlib.Data.Set.Finite.lean")

    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    mwe = Mwe(
        code,
        "finite_def",
    )
    mwe.rewrite_to_tactic_style()
    theorem_string = """ by exact (
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩
)"""
    assert mwe.code[mwe.proof_start : mwe.proof_end] == theorem_string
