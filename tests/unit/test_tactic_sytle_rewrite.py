from tests.utils.utils import initiate_mwe_for_finite_def


def test_extracted_theorem_interaction_in_gym() -> None:
    mwe = initiate_mwe_for_finite_def()

    mwe.rewrite_to_tactic_style()
    theorem_string = """ by exact (
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩)\n"""
    assert mwe.code[mwe.proof_start : mwe.proof_end] == theorem_string
