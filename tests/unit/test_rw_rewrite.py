from tests.utils.utils import initiate_mwe_for_rw, initiate_mwe_for_rw_2


def test_rewrite_theorem_with_expanded_rw() -> None:
    mwe = initiate_mwe_for_rw()

    mwe.rewrite_expand_rw()
    theorem_string = """ by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]\n"""
    assert mwe.code[mwe.proof_start : mwe.proof_end] == theorem_string


def test_rewrite_theorem_with_expanded_rw_two_rw_matches() -> None:
    mwe = initiate_mwe_for_rw_2()

    mwe.rewrite_expand_rw()
    theorem_string = """ by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right]; rw [h]; rw [Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs]; rw [InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]\n"""
    assert mwe.code[mwe.proof_start : mwe.proof_end] == theorem_string
