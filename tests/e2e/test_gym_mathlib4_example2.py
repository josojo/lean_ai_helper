from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import initiate_mwe_for_disjoint_to_finset


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""

    mwe = initiate_mwe_for_disjoint_to_finset()

    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tac(
            state_0,
            "@disjoint_toFinset _ _ _ hs.fintype ht.fintype",
        )
        assert isinstance(state_1, ProofFinished)
