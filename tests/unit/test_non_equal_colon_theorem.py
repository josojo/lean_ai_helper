import pytest
from src.mwe import Mwe, UnusualTheoremFormatError
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("../data/theorem.without.equal.colon.notation.lean")
    with pytest.raises(
        UnusualTheoremFormatError,
        match="Theorem isNat_ratCast is not according to the standard format with =:",
    ):
        Mwe(
            code,
            "isNat_ratCast",
        )
