from src.interaction.gym import Gym, ProofFinished
from src.mwe import Mwe
from tests.utils.utils import read_code_from_file


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = read_code_from_file("../data/Mathlib.Data.Set.Finite.lean")

    mwe = Mwe(
        code,
        "disjoint_toFinset",
    )

    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tac(
            state_0,
            "@disjoint_toFinset _ _ _ hs.fintype ht.fintype",
        )
        assert isinstance(state_1, ProofFinished)
