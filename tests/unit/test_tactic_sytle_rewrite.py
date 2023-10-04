from src.mwe import Mwe
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("../data/Mathlib.Data.Set.Finite.lean")

    mwe = Mwe(
        code,
        "finite_def",
    )
    mwe.rewrite_to_tactic_style()
    theorem_string = """ by exact (
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩)\n"""
    assert mwe.code[mwe.proof_start : mwe.proof_end] == theorem_string
