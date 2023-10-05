import pytest
from src.mwe import Mwe, UnusualTheoremFormatError
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("./tests/data/theorem.with.equal.colon.in.defintion.lean")
    with pytest.raises(
        UnusualTheoremFormatError,
        match="Theorem IsRat.to_isNat is not according to the standard format with =:",
    ):
        Mwe(
            code,
            "IsRat.to_isNat",
        )
