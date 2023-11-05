/-
Test file used for testing the splitting of rw functions
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

#align_import geometry.euclidean.angle.oriented.right_angle from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Oriented angles in right-angled triangles.

This file proves basic geometrical results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace Orientation

open FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable [hd2 : Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two Orientation.oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arccos (‖y‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h
#align orientation.oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two Orientation.oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two Orientation.oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arcsin (‖x‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h
#align orientation.oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two Orientation.oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_of_oangle_eq_pi_div_two h)]
#align orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arctan (‖x‖ / ‖y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h
#align orientation.oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two Orientation.oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.cos_oangle_add_right_of_oangle_eq_pi_div_two Orientation.cos_oangle_add_right_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h
#align orientation.cos_oangle_add_left_of_oangle_eq_pi_div_two Orientation.cos_oangle_add_left_of_oangle_eq_pi_div_two
