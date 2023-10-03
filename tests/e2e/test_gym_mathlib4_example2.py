import os
from src.interaction.gym import Gym, ProofFinished
from src.mwe import Mwe


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = ""
    # Get the absolute path to the directory of the current script
    script_dir = os.path.dirname(os.path.realpath(__file__))

    # Join the script directory with the relative path to the file
    file_path = os.path.join(script_dir, "../data/Mathlib.Data.Set.Finite.lean")

    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

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
