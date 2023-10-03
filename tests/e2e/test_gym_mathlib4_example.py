import os
from src.interaction.gym import Gym, ProofFinished
from src.mwe import Mwe


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    code = ""
    # Get the absolute path to the directory of the current script
    script_dir = os.path.dirname(os.path.realpath(__file__))

    # Join the script directory with the relative path to the file
    file_path = os.path.join(script_dir, "../data/Mathlib.Meta.NormNum.Prime.lean")

    # Open the file using the absolute path
    file = open(file_path, "r", encoding="utf-8")
    code = file.read()
    file.close()

    mwe = Mwe(
        code,
        "minFacHelper_0",
    )
    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tac(
            state_0,
            "by refine \u27e8by norm_num, by norm_num, ?_\u27e9 \n  refine (le_minFac'.mpr \u03bb p hp hpn \u21a6 ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))\n rcases hp.eq_or_lt with rfl|h\n \u00b7 simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2 \n \u00b7 exact h",
        )
        assert isinstance(state_1, ProofFinished)
