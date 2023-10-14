from src.mwe import Mwe


from src.interaction.gym import Gym
from tests.utils.utils import read_code_from_file


def test_extracted_theorem_interaction_in_gym() -> None:
    code = read_code_from_file("./tests/data/preludeimport.lean")
    # produces the following crash error:
    # Main.lean:572:2: error: unknown constant 'Mathlib.Tactic.Ring.zero_pow.match_1'
    mwe = Mwe(
        code,
        "Nat.lt_add_of_zero_lt_left",
    )
    gym = Gym(mwe)
    modified_code = gym._modify_proof()  # pylint: disable=protected-access

    assert (
        modified_code[:227]
        == """
/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean4Repl

import Mathlib.Init.Data.Nat.Lemmas
"""
    )
