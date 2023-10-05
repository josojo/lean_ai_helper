/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Parser
import Std.Lean.Meta.DiscrTree
import Mathlib.Algebra.Invertible
import Mathlib.Data.Rat.Cast
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Conv
import Mathlib.Util.Qq

/-!
## `norm_num` core functionality

This file sets up the `norm_num` tactic and the `@[norm_num]` attribute,
which allow for plugging in new normalization functionality around a simp-based driver.
The actual behavior is in `@[norm_num]`-tagged definitions in `Tactic.NormNum.Basic`
and elsewhere.
-/
open Lean hiding Rat mkRat
open Lean.Meta Qq Lean.Elab Term

/-- Attribute for identifying `norm_num` extensions. -/
syntax (name := norm_num) "norm_num " term,+ : attr

namespace Mathlib
namespace Meta.NormNum

initialize registerTraceClass `Tactic.norm_num

/-- Assert that an element of a semiring is equal to the coercion of some natural number. -/
structure IsNat [AddMonoidWithOne α] (a : α) (n : ℕ) : Prop where
  /-- The element is equal to the coercion of the natural number. -/
  out : a = n

theorem IsNat.raw_refl (n : ℕ) : IsNat n n := ⟨rfl⟩

/--
A "raw nat cast" is an expression of the form `(Nat.rawCast lit : α)` where `lit` is a raw
natural number literal. These expressions are used by tactics like `ring` to decrease the number
of typeclass arguments required in each use of a number literal at type `α`.
-/
@[simp] def _root_.Nat.rawCast [AddMonoidWithOne α] (n : ℕ) : α := n

theorem IsNat.to_eq [AddMonoidWithOne α] {n} : {a a' : α} → IsNat a n → n = a' → a = a'
  | _, _, ⟨rfl⟩, rfl => rfl

theorem IsNat.to_raw_eq [AddMonoidWithOne α] : IsNat (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsNat.of_raw (α) [AddMonoidWithOne α] (n : ℕ) : IsNat (n.rawCast : α) n := ⟨rfl⟩

@[elab_as_elim]
theorem isNat.natElim {p : ℕ → Prop} : {n : ℕ} → {n' : ℕ} → IsNat n n' → p n' → p n
  | _, _, ⟨rfl⟩, h => h

/-- Assert that an element of a ring is equal to the coercion of some integer. -/
structure IsInt [Ring α] (a : α) (n : ℤ) : Prop where
  /-- The element is equal to the coercion of the integer. -/
  out : a = n

/--
A "raw int cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal

(That is, we only actually use this function for negative integers.) This representation is used by
tactics like `ring` to decrease the number of typeclass arguments required in each use of a number
literal at type `α`.
-/
@[simp] def _root_.Int.rawCast [Ring α] (n : ℤ) : α := n

theorem IsInt.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsInt a (.ofNat n) → IsNat a n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsNat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsInt.to_raw_eq [Ring α] : IsInt (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsInt.of_raw (α) [Ring α] (n : ℤ) : IsInt (n.rawCast : α) n := ⟨rfl⟩

theorem IsInt.neg_to_eq {α} [Ring α] {n} :
    {a a' : α} → IsInt a (.negOfNat n) → n = a' → a = -a'
  | _, _, ⟨rfl⟩, rfl => by simp [Int.negOfNat_eq, Int.cast_neg]

theorem IsInt.nonneg_to_eq {α} [Ring α] {n}
    {a a' : α} (h : IsInt a (.ofNat n)) (e : n = a') : a = a' := h.to_isNat.to_eq e

/-- Represent an integer as a typed expression. -/
def mkRawIntLit (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := mkRawNatLit n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/-- Extract the integer from a raw integer literal, as produced by
`Mathlib.Meta.NormNum.mkRawIntLit`. -/
def _root_.Lean.Expr.intLit! (e : Expr) : ℤ :=
  if e.isAppOfArity ``Int.ofNat 1 then
    e.appArg!.natLit!
  else if e.isAppOfArity ``Int.negOfNat 1 then
    .negOfNat e.appArg!.natLit!
  else
    panic! "not a raw integer literal"

/-- Extract the raw natlit representing the absolute value of a raw integer literal
(of the type produced by `Mathlib.Meta.NormNum.mkRawIntLit`) along with an equality proof. -/
def rawIntLitNatAbs (n : Q(ℤ)) : (m : Q(ℕ)) × Q(Int.natAbs $n = $m) :=
  if n.isAppOfArity ``Int.ofNat 1 then
    have m : Q(ℕ) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.ofNat $m) = $m) from q(Int.natAbs_ofNat $m)⟩
  else if n.isAppOfArity ``Int.negOfNat 1 then
    have m : Q(ℕ) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.negOfNat $m) = $m) from q(Int.natAbs_neg $m)⟩
  else
    panic! "not a raw integer literal"

/-- A shortcut (non)instance for `AddMonoidWithOne ℕ` to shrink generated proofs. -/
def instAddMonoidWithOneNat : AddMonoidWithOne ℕ := inferInstance

/-- A shortcut (non)instance for `Ring ℤ` to shrink generated proofs. -/
def instRingInt : Ring ℤ := inferInstance

/--
Assert that an element of a ring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
inductive IsRat [Ring α] (a : α) (num : ℤ) (denom : ℕ) : Prop
  | mk (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

/--
A "raw rat cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal
* `(Rat.rawCast n d : α)` where `n` is a raw int cast, `d` is a raw nat cast, and `d` is not 1 or 0.

This representation is used by tactics like `ring` to decrease the number of typeclass arguments
required in each use of a number literal at type `α`.
-/
@[simp]
def _root_.Rat.rawCast [DivisionRing α] (n : ℤ) (d : ℕ) : α := n / d

theorem IsRat.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsRat a (.ofNat n) (nat_lit 1) → IsNat a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩
