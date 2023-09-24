import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.NormNum.Basic

#align_import data.nat.prime_norm_num from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"
open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

theorem not_prime_mul_of_ble (a b n : ℕ) (h : a * b = n) (h₁ : a.ble 1 = false)
    (h₂ : b.ble 1 = false) : ¬ n.Prime :=
  not_prime_mul' h (ble_eq_false.mp h₁) (ble_eq_false.mp h₂)

    /-- Produce a proof that `n` is not prime from a factor `1 < d < n`. `en` should be the expression
    that is the natural number literal `n`. -/
def deriveNotPrime (n d : ℕ) (en : Q(ℕ)) : Q(¬ Nat.Prime $en) := Id.run <| do
  let d' : ℕ := n / d
  let prf : Q($d * $d' = $en) := (q(Eq.refl $en) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(not_prime_mul_of_ble _ _ _ $prf $r $r')

    /-- A predicate representing partial progress in a proof of `minFac`. -/
def MinFacHelper (n k : ℕ) : Prop :=
  2 < k ∧ k % 2 = 1 ∧ k ≤ minFac n

theorem MinFacHelper.one_lt {n k : ℕ} (h : MinFacHelper n k) : 1 < n := by
    have : 2 < minFac n := h.1.trans_le h.2.2
    rcases eq_zero_or_pos n with rfl|h
    · contradiction
    rcases (succ_le_of_lt h).eq_or_lt with rfl|h
    · contradiction
    exact h

theorem minFacHelper_0 (n : ℕ)
    (h1 : Nat.ble (nat_lit 2) n = true) (h2 : nat_lit 1 = n % (nat_lit 2)) :
    MinFacHelper n (nat_lit 3) := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    refine (le_minFac'.mpr λ p hp hpn ↦ ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))
    rcases hp.eq_or_lt with rfl|h
    · simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2
    · exact h