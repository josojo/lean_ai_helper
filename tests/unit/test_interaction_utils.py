import unittest

from src.interaction.utils import (
    undo_line_splits_for_dot_notation,
    undo_line_splits_for_unclosed_parenthesis,
    format_tatic_for_repl,
)


class TestUndoLineSplits(unittest.TestCase):
    def test_undo_line_splits_for_unclosed_brackets(self):
        """Undo line splits for unclosed parenthesis."""
        commands = [
            "rw [\u2190 h3, mul_comm n1, mul_assoc n2, \u2190 mul_assoc n1, h1,",
            "      \u2190 mul_assoc n2, mul_comm n2, mul_assoc, h2]",
        ]

        expected = [
            "rw [\u2190 h3, mul_comm n1, mul_assoc n2, \u2190 mul_assoc n1, h1,\n      \u2190 mul_assoc n2, mul_comm n2, mul_assoc, h2]"
        ]
        self.assertEqual(undo_line_splits_for_unclosed_parenthesis(commands), expected)

        commands = [
            "haveI : DecidablePred p := fun i \u21a6 Classical.propDecidable (p i)",
            "  exact \u27e8fun i => if hi : p i then f \u27e8i, hi\u27e9 else Classical.choice (ne i), \n funext fun i \u21a6 dif_pos i.2\u27e9",
        ]
        expected = [
            "haveI : DecidablePred p := fun i \u21a6 Classical.propDecidable (p i)",
            "  exact \u27e8fun i => if hi : p i then f \u27e8i, hi\u27e9 else Classical.choice (ne i), \n funext fun i \u21a6 dif_pos i.2\u27e9",
        ]
        self.assertEqual(undo_line_splits_for_unclosed_parenthesis(commands), expected)

    def test_undo_line_splits_for_dot_notation(self):
        # Test case 1: No dot notation
        commands = ["\u00b7 rw [add_mod, mod_self, add_zero, mod_mod]", " exact h.2.1"]
        expected = ["\u00b7 rw [add_mod, mod_self, add_zero, mod_mod]\n exact h.2.1"]
        self.assertEqual(undo_line_splits_for_dot_notation(commands), expected)

        # Test case 2: Dot notation without line split
        commands = ["\u00b7 rw [add_mod, mod_self, add_zero, mod_mod]", "exact h.2.1"]
        expected = ["\u00b7 rw [add_mod, mod_self, add_zero, mod_mod]", "exact h.2.1"]
        self.assertEqual(undo_line_splits_for_dot_notation(commands), expected)

        # Test case 3: Dot notatiddon with line split
        commands = ["rw [add_mod, mod_self, add_zero, mod_mod]", " exact h.2.1"]
        expected = ["rw [add_mod, mod_self, add_zero, mod_mod]", " exact h.2.1"]
        self.assertEqual(undo_line_splits_for_dot_notation(commands), expected)

        commands = [
            "refine ⟨by norm_num, by norm_num, ?_⟩",
            "refine (le_minFac'.mpr λ p hp hpn ↦ ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))",
            "rcases hp.eq_or_lt with rfl|h",
            "· simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2",
            "· exact h",
        ]
        expected = [
            "refine ⟨by norm_num, by norm_num, ?_⟩",
            "refine (le_minFac'.mpr λ p hp hpn ↦ ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))",
            "rcases hp.eq_or_lt with rfl|h",
            "· simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2",
            "· exact h",
        ]
        self.assertEqual(undo_line_splits_for_dot_notation(commands), expected)

    def test_format_tatic_for_repl(self):
        test_str = " by\n rw [\u2190 Finset.coe_ssubset, Finite.coe_toFins]"
        self.assertEqual(
            format_tatic_for_repl(test_str),
            ["rw [\u2190 Finset.coe_ssubset, Finite.coe_toFins]"],
        )

    def test_format_tatic_for_repl_2(self):
        # happend with apply Submodule.map_comap_le
        test_str = " by\n rw [\u2190 Finset.coe_ssubset, Finite.coe_toFins]; simp\n"
        self.assertEqual(
            format_tatic_for_repl(test_str),
            ["rw [\u2190 Finset.coe_ssubset, Finite.coe_toFins]", " simp"],
        )


if __name__ == "__main__":
    unittest.main()
