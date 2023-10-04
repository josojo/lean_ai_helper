from src.interaction.gym import Gym, ProofFinished
from tests.utils.utils import initiate_mwe_for_min_fac_helper


def test_example_1() -> None:
    """Test the example from https://leanprover-community.github.io/mwe.html."""
    mwe = initiate_mwe_for_min_fac_helper()
    with Gym(mwe) as (gym, state_0):
        state_1 = gym.run_tac(
            state_0,
            "by refine \u27e8by norm_num, by norm_num, ?_\u27e9 \n\
    refine (le_minFac'.mpr \u03bb p hp hpn \u21a6 ?_).resolve_left \
    (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))\n rcases hp.eq_or_lt with rfl|h\n \u00b7 \
    simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2 \n \u00b7 exact h",
        )
        assert isinstance(state_1, ProofFinished)
