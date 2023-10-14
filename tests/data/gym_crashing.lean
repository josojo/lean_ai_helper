/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Tim Baanen
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Clear!
import Mathlib.Util.AtomM

/-!
# `ring` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions (`a * b`)
- scalar multiplication of expressions (`n • a`; the multiplier must have type `ℕ`)
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The extension to exponents means that something like `2 * 2^n * b = b * 2^(n+1)` can be proved,
even though it is not strictly speaking an equation in the language of commutative rings.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
The normalisation is guided by building a value in the type `ExSum` at the meta level,
together with a proof (at the base level) that the original value is equal to
the normalised version.

The outline of the file:
- Define a mutual inductive family of types `ExSum`, `ExProd`, `ExBase`,
  which can represent expressions with `+`, `*`, `^` and rational numerals.
  The mutual induction ensures that associativity and distributivity are applied,
  by restricting which kinds of subexpressions appear as arguments to the various operators.
- Represent addition, multiplication and exponentiation in the `ExSum` type,
  thus allowing us to map expressions to `ExSum` (the `eval` function drives this).
  We apply associativity and distributivity of the operators here (helped by `Ex*` types)
  and commutativity as well (by sorting the subterms; unfortunately not helped by anything).
  Any expression not of the above formats is treated as an atom (the same as a variable).

There are some details we glossed over which make the plan more complicated:
- The order on atoms is not initially obvious.
  We construct a list containing them in order of initial appearance in the expression,
  then use the index into the list as a key to order on.
- For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
  We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
  as soon as we deal with exponents.

## Caveats and future work

The normalized form of an expression is the one that is useful for the tactic,
but not as nice to read. To remedy this, the user-facing normalization calls `ringNFCore`.

Subtraction cancels out identical terms, but division does not.
That is: `a - a = 0 := by ring` solves the goal,
but `a / a := 1 by ring` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/

namespace Mathlib.Tactic
namespace Ring
open Mathlib.Meta Qq NormNum Lean.Meta AtomM
open Lean (MetaM Expr mkRawNatLit)

def instCommSemiringNat : CommSemiring ℕ := inferInstance

def sℕ : Q(CommSemiring ℕ) := q(instCommSemiringNat)

set_option relaxedAutoImplicit true

mutual

inductive ExBase : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → (e : Q($α)) → Type
  | atom (id : ℕ) : ExBase sα e
  | sum (_ : ExSum sα e) : ExBase sα e

inductive ExProd : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → (e : Q($α)) → Type
  | const (value : ℚ) (hyp : Option Expr := none) : ExProd sα e
  | mul {α : Q(Type u)} {sα : Q(CommSemiring $α)} {x : Q($α)} {e : Q(ℕ)} {b : Q($α)} :
    ExBase sα x → ExProd sℕ e → ExProd sα b → ExProd sα q($x ^ $e * $b)

inductive ExSum : ∀ {α : Q(Type u)}, Q(CommSemiring $α) → (e : Q($α)) → Type
  | zero {α : Q(Type u)} {sα : Q(CommSemiring $α)} : ExSum sα q(0 : $α)
  | add {α : Q(Type u)} {sα : Q(CommSemiring $α)} {a b : Q($α)} :
    ExProd sα a → ExSum sα b → ExSum sα q($a + $b)
end

mutual -- partial only to speed up compilation

partial def ExBase.eq : ExBase sα a → ExBase sα b → Bool
  | .atom i, .atom j => i == j
  | .sum a, .sum b => a.eq b
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExProd.eq : ExProd sα a → ExProd sα b → Bool
  | .const i _, .const j _ => i == j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => a₁.eq b₁ && a₂.eq b₂ && a₃.eq b₃
  | _, _ => false

@[inherit_doc ExBase.eq]
partial def ExSum.eq : ExSum sα a → ExSum sα b → Bool
  | .zero, .zero => true
  | .add a₁ a₂, .add b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false
end

mutual -- partial only to speed up compilation
partial def ExBase.cmp : ExBase sα a → ExBase sα b → Ordering
  | .atom i, .atom j => compare i j
  | .sum a, .sum b => a.cmp b
  | .atom .., .sum .. => .lt
  | .sum .., .atom .. => .gt

@[inherit_doc ExBase.cmp]
partial def ExProd.cmp : ExProd sα a → ExProd sα b → Ordering
  | .const i _, .const j _ => compare i j
  | .mul a₁ a₂ a₃, .mul b₁ b₂ b₃ => (a₁.cmp b₁).then (a₂.cmp b₂) |>.then (a₃.cmp b₃)
  | .const _ _, .mul .. => .lt
  | .mul .., .const _ _ => .gt

@[inherit_doc ExBase.cmp]
partial def ExSum.cmp : ExSum sα a → ExSum sα b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt
end

instance : Inhabited (Σ e, (ExBase sα) e) := ⟨default, .atom 0⟩
instance : Inhabited (Σ e, (ExSum sα) e) := ⟨_, .zero⟩
instance : Inhabited (Σ e, (ExProd sα) e) := ⟨default, .const 0 none⟩

mutual

partial def ExBase.cast : ExBase sα a → Σ a, ExBase sβ a
  | .atom i => ⟨a, .atom i⟩
  | .sum a => let ⟨_, vb⟩ := a.cast; ⟨_, .sum vb⟩

partial def ExProd.cast : ExProd sα a → Σ a, ExProd sβ a
  | .const i h => ⟨a, .const i h⟩
  | .mul a₁ a₂ a₃ => ⟨_, .mul a₁.cast.2 a₂ a₃.cast.2⟩

partial def ExSum.cast : ExSum sα a → Σ a, ExSum sβ a
  | .zero => ⟨_, .zero⟩
  | .add a₁ a₂ => ⟨_, .add a₁.cast.2 a₂.cast.2⟩

end

structure Result {α : Q(Type u)} (E : Q($α) → Type) (e : Q($α)) where
  expr : Q($α)
  val : E expr
  proof : Q($e = $expr)

instance [Inhabited (Σ e, E e)] : Inhabited (Result E e) :=
  let ⟨e', v⟩ : Σ e, E e := default; ⟨e', v, default⟩

variable {α : Q(Type u)} (sα : Q(CommSemiring $α)) [CommSemiring R]

def ExProd.mkNat (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q(($lit).rawCast : $α), .const n none⟩

def ExProd.mkNegNat (_ : Q(Ring $α)) (n : ℕ) : (e : Q($α)) × ExProd sα e :=
  let lit : Q(ℕ) := mkRawNatLit n
  ⟨q((Int.negOfNat $lit).rawCast : $α), .const (-n) none⟩

def ExProd.mkRat (_ : Q(DivisionRing $α)) (q : ℚ) (n : Q(ℤ)) (d : Q(ℕ)) (h : Expr) :
    (e : Q($α)) × ExProd sα e :=
  ⟨q(Rat.rawCast $n $d : $α), .const q h⟩

section
variable {sα}

def ExBase.toProd (va : ExBase sα a) (vb : ExProd sℕ b) :
  ExProd sα q($a ^ $b * (nat_lit 1).rawCast) := .mul va vb (.const 1 none)

def ExProd.toSum (v : ExProd sα e) : ExSum sα q($e + 0) := .add v .zero

def ExProd.coeff : ExProd sα e → ℚ
  | .const q _ => q
  | .mul _ _ v => v.coeff
end

inductive Overlap (e : Q($α)) where
  | zero (_ : Q(IsNat $e (nat_lit 0)))
  | nonzero (_ : Result (ExProd sα) e)

theorem add_overlap_pf (x : R) (e) (pq_pf : a + b = c) :
    x ^ e * a + x ^ e * b = x ^ e * c := by subst_vars; simp [mul_add]

theorem add_overlap_pf_zero (x : R) (e) :
    IsNat (a + b) (nat_lit 0) → IsNat (x ^ e * a + x ^ e * b) (nat_lit 0)
  | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

def evalAddOverlap (va : ExProd sα a) (vb : ExProd sα b) : Option (Overlap sα q($a + $b)) :=
  match va, vb with
  | .const za ha, .const zb hb => do
    let ra := Result.ofRawRat za a ha; let rb := Result.ofRawRat zb b hb
    let res ← NormNum.evalAdd.core q($a + $b) q(HAdd.hAdd) a b ra rb
    match res with
    | .isNat _ (.lit (.natVal 0)) p => pure <| .zero p
    | rc =>
      let ⟨zc, hc⟩ ← rc.toRatNZ
      let ⟨c, pc⟩ := rc.toRawEq
      pure <| .nonzero ⟨c, .const zc hc, pc⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul vb₁ vb₂ vb₃ => do
    guard (va₁.eq vb₁ && va₂.eq vb₂)
    match ← evalAddOverlap va₃ vb₃ with
    | .zero p => pure <| .zero (q(add_overlap_pf_zero $a₁ $a₂ $p) : Expr)
    | .nonzero ⟨_, vc, p⟩ =>
      pure <| .nonzero ⟨_, .mul va₁ va₂ vc, (q(add_overlap_pf $a₁ $a₂ $p) : Expr)⟩
  | _, _ => none

theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

theorem add_pf_add_overlap
    (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm]

theorem add_pf_add_overlap_zero
    (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
  subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
  subst_vars; simp [add_left_comm]

partial def evalAdd (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a + $b) :=
  match va, vb with
  | .zero, vb => ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    match evalAddOverlap sα va₁ vb₁ with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ := evalAdd va₂ vb₂
      ⟨_, .add vc₁ vc₂, q(add_pf_add_overlap $pc₁ $pc₂)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ := evalAdd va₂ vb₂
      ⟨c₂, vc₂, q(add_pf_add_overlap_zero $pc₁ $pc₂)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
        let ⟨_c, vc, (pc : Q($_a₂ + ($b₁ + $_b₂) = $_c))⟩ := evalAdd va₂ vb
        ⟨_, .add va₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, (pc : Q($a₁ + $_a₂ + $_b₂ = $_c))⟩ := evalAdd va vb₂
        ⟨_, .add vb₁ vc, q(add_pf_add_gt $b₁ $pc)⟩

theorem one_mul (a : R) : (nat_lit 1).rawCast * a = a := by simp [Nat.rawCast]

theorem mul_one (a : R) : a * (nat_lit 1).rawCast = a := by simp [Nat.rawCast]

theorem mul_pf_left (a₁ : R) (a₂) (_ : a₃ * b = c) : (a₁ ^ a₂ * a₃ : R) * b = a₁ ^ a₂ * c := by
  subst_vars; rw [mul_assoc]

theorem mul_pf_right (b₁ : R) (b₂) (_ : a * b₃ = c) : a * (b₁ ^ b₂ * b₃) = b₁ ^ b₂ * c := by
  subst_vars; rw [mul_left_comm]

theorem mul_pp_pf_overlap (x : R) (_ : ea + eb = e) (_ : a₂ * b₂ = c) :
    (x ^ ea * a₂ : R) * (x ^ eb * b₂) = x ^ e * c := by
  subst_vars; simp [pow_add, mul_mul_mul_comm]

partial def evalMulProd (va : ExProd sα a) (vb : ExProd sα b) : Result (ExProd sα) q($a * $b) :=
  match va, vb with
  | .const za ha, .const zb hb =>
    if za = 1 then
      ⟨b, .const zb hb, (q(one_mul $b) : Expr)⟩
    else if zb = 1 then
      ⟨a, .const za ha, (q(mul_one $a) : Expr)⟩
    else
      let ra := Result.ofRawRat za a ha; let rb := Result.ofRawRat zb b hb
      let rc := (NormNum.evalMul.core q($a * $b) q(HMul.hMul) _ _
          q(CommSemiring.toSemiring) ra rb).get!
      let ⟨zc, hc⟩ := rc.toRatNZ.get!
      let ⟨c, pc⟩ :=  rc.toRawEq
      ⟨c, .const zc hc, pc⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .const _ _ =>
    let ⟨_, vc, pc⟩ := evalMulProd va₃ vb
    ⟨_, .mul va₁ va₂ vc, (q(mul_pf_left $a₁ $a₂ $pc) : Expr)⟩
  | .const _ _, .mul (x := b₁) (e := b₂) vb₁ vb₂ vb₃ =>
    let ⟨_, vc, pc⟩ := evalMulProd va vb₃
    ⟨_, .mul vb₁ vb₂ vc, (q(mul_pf_right $b₁ $b₂ $pc) : Expr)⟩
  | .mul (x := xa) (e := ea) vxa vea va₂, .mul (x := xb) (e := eb) vxb veb vb₂ => Id.run do
    if vxa.eq vxb then
      if let some (.nonzero ⟨_, ve, pe⟩) := evalAddOverlap sℕ vea veb then
        let ⟨_, vc, pc⟩ := evalMulProd va₂ vb₂
        return ⟨_, .mul vxa ve vc, (q(mul_pp_pf_overlap $xa $pe $pc) : Expr)⟩
    if let .lt := (vxa.cmp vxb).then (vea.cmp veb) then
      let ⟨_, vc, pc⟩ := evalMulProd va₂ vb
      ⟨_, .mul vxa vea vc, (q(mul_pf_left $xa $ea $pc) : Expr)⟩
    else
      let ⟨_, vc, pc⟩ := evalMulProd va vb₂
      ⟨_, .mul vxb veb vc, (q(mul_pf_right $xb $eb $pc) : Expr)⟩

theorem mul_zero (a : R) : a * 0 = 0 := by simp

theorem mul_add (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
    a * (b₁ + b₂) = d := by subst_vars; simp [_root_.mul_add]

def evalMul₁ (va : ExProd sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a * $b) :=
  match vb with
  | .zero => ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalMulProd sα va vb₁
    let ⟨_, vc₂, pc₂⟩ := evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ := evalAdd sα vc₁.toSum vc₂
    ⟨_, vd, q(mul_add $pc₁ $pc₂ $pd)⟩

theorem zero_mul (b : R) : 0 * b = 0 := by simp

theorem add_mul (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
    (a₁ + a₂) * b = d := by subst_vars; simp [_root_.add_mul]

def evalMul (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a * $b) :=
  match va with
  | .zero => ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ =>
    let ⟨_, vc₁, pc₁⟩ := evalMul₁ sα va₁ vb
    let ⟨_, vc₂, pc₂⟩ := evalMul va₂ vb
    let ⟨_, vd, pd⟩ := evalAdd sα vc₁ vc₂
    ⟨_, vd, q(add_mul $pc₁ $pc₂ $pd)⟩

theorem natCast_nat (n) : ((Nat.rawCast n : ℕ) : R) = Nat.rawCast n := by simp

theorem natCast_mul (a₂) (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₃ : ℕ) : R) = b₃) :
    ((a₁ ^ a₂ * a₃ : ℕ) : R) = b₁ ^ a₂ * b₃ := by subst_vars; simp

theorem natCast_zero : ((0 : ℕ) : R) = 0 := by exact ( Nat.cast_zero)

theorem natCast_add (_ : ((a₁ : ℕ) : R) = b₁) (_ : ((a₂ : ℕ) : R) = b₂) :
    ((a₁ + a₂ : ℕ) : R) = b₁ + b₂ := by subst_vars; simp

mutual

partial def ExBase.evalNatCast (va : ExBase sℕ a) : AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    let a' : Q($α) := q($a)
    let i ← addAtom a'
    pure ⟨a', ExBase.atom i, (q(Eq.refl $a') : Expr)⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← va.evalNatCast
    pure ⟨_, .sum vc, p⟩

partial def ExProd.evalNatCast (va : ExProd sℕ a) : AtomM (Result (ExProd sα) q($a)) :=
  match va with
  | .const c hc =>
    have n : Q(ℕ) := a.appArg!
    pure ⟨q(Nat.rawCast $n), .const c hc, (q(natCast_nat (R := $α) $n) : Expr)⟩
  | .mul (e := a₂) va₁ va₂ va₃ => do
    let ⟨_, vb₁, pb₁⟩ ← va₁.evalNatCast
    let ⟨_, vb₃, pb₃⟩ ← va₃.evalNatCast
    pure ⟨_, .mul vb₁ va₂ vb₃, q(natCast_mul $a₂ $pb₁ $pb₃)⟩

partial def ExSum.evalNatCast (va : ExSum sℕ a) : AtomM (Result (ExSum sα) q($a)) :=
  match va with
  | .zero => pure ⟨_, .zero, q(natCast_zero (R := $α))⟩
  | .add va₁ va₂ => do
    let ⟨_, vb₁, pb₁⟩ ← va₁.evalNatCast
    let ⟨_, vb₂, pb₂⟩ ← va₂.evalNatCast
    pure ⟨_, .add vb₁ vb₂, q(natCast_add $pb₁ $pb₂)⟩

end

theorem smul_nat (_ : (a * b : ℕ) = c) : a • b = c := by subst_vars; simp

theorem smul_eq_cast (_ : ((a : ℕ) : R) = a') (_ : a' * b = c) : a • b = c := by subst_vars; simp

def evalNSMul (va : ExSum sℕ a) (vb : ExSum sα b) : AtomM (Result (ExSum sα) q($a • $b)) := do
  if ← isDefEq sα sℕ then
    let ⟨_, va'⟩ := va.cast
    have _b : Q(ℕ) := b
    let ⟨(_c : Q(ℕ)), vc, (pc : Q($a * $_b = $_c))⟩ := evalMul sα va' vb
    pure ⟨_, vc, (q(smul_nat $pc) : Expr)⟩
  else
    let ⟨_, va', pa'⟩ ← va.evalNatCast sα
    let ⟨_, vc, pc⟩ := evalMul sα va' vb
    pure ⟨_, vc, (q(smul_eq_cast $pa' $pc) : Expr)⟩

theorem neg_one_mul {R} [Ring R] {a b : R} (_ : (Int.negOfNat (nat_lit 1)).rawCast * a = b) :
    -a = b := by subst_vars; simp [Int.negOfNat]

theorem neg_mul {R} [Ring R] (a₁ : R) (a₂) {a₃ b : R}
    (_ : -a₃ = b) : -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b := by subst_vars; simp

def evalNegProd (rα : Q(Ring $α)) (va : ExProd sα a) : Result (ExProd sα) q(-$a) :=
  match va with
  | .const za ha =>
    let lit : Q(ℕ) := mkRawNatLit 1
    let ⟨m1, _⟩ := ExProd.mkNegNat sα rα 1
    let rm := Result.isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)
    let ra := Result.ofRawRat za a ha
    let rb := (NormNum.evalMul.core q($m1 * $a) q(HMul.hMul) _ _
      q(CommSemiring.toSemiring) rm ra).get!
    let ⟨zb, hb⟩ := rb.toRatNZ.get!
    let ⟨b, (pb : Q((Int.negOfNat (nat_lit 1)).rawCast * $a = $b))⟩ := rb.toRawEq
    ⟨b, .const zb hb, (q(neg_one_mul (R := $α) $pb) : Expr)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨_, vb, pb⟩ := evalNegProd rα va₃
    ⟨_, .mul va₁ va₂ vb, (q(neg_mul $a₁ $a₂ $pb) : Expr)⟩

theorem neg_zero {R} [Ring R] : -(0 : R) = 0 := by simp

theorem neg_add {R} [Ring R] {a₁ a₂ b₁ b₂ : R}
    (_ : -a₁ = b₁) (_ : -a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂ := by subst_vars; simp [add_comm]

def evalNeg (rα : Q(Ring $α)) (va : ExSum sα a) : Result (ExSum sα) q(-$a) :=
  match va with
  | .zero => ⟨_, .zero, (q(neg_zero (R := $α)) : Expr)⟩
  | .add va₁ va₂ =>
    let ⟨_, vb₁, pb₁⟩ := evalNegProd sα rα va₁
    let ⟨_, vb₂, pb₂⟩ := evalNeg rα va₂
    ⟨_, .add vb₁ vb₂, (q(neg_add $pb₁ $pb₂) : Expr)⟩

theorem sub_pf {R} [Ring R] {a b c d : R}
    (_ : -b = c) (_ : a + c = d) : a - b = d := by subst_vars; simp [sub_eq_add_neg]

def evalSub (rα : Q(Ring $α)) (va : ExSum sα a) (vb : ExSum sα b) : Result (ExSum sα) q($a - $b) :=
  let ⟨_c, vc, pc⟩ := evalNeg sα rα vb
  let ⟨d, vd, (pd : Q($a + $_c = $d))⟩ := evalAdd sα va vc
  ⟨d, vd, (q(sub_pf $pc $pd) : Expr)⟩

theorem pow_prod_atom (a : R) (b) : a ^ b = (a + 0) ^ b * (nat_lit 1).rawCast := by simp

def evalPowProdAtom (va : ExProd sα a) (vb : ExProd sℕ b) : Result (ExProd sα) q($a ^ $b) :=
  ⟨_, (ExBase.sum va.toSum).toProd vb, q(pow_prod_atom $a $b)⟩

theorem pow_atom (a : R) (b) : a ^ b = a ^ b * (nat_lit 1).rawCast + 0 := by simp

def evalPowAtom (va : ExBase sα a) (vb : ExProd sℕ b) : Result (ExSum sα) q($a ^ $b) :=
  ⟨_, (va.toProd vb).toSum, q(pow_atom $a $b)⟩

theorem const_pos (n : ℕ) (h : Nat.ble 1 n = true) : 0 < (n.rawCast : ℕ) := by exact ( Nat.le_of_ble_eq_true h)

theorem mul_exp_pos (n) (h₁ : 0 < a₁) (h₂ : 0 < a₂) : 0 < a₁ ^ n * a₂ := by exact (
  Nat.mul_pos (Nat.pos_pow_of_pos _ h₁) h₂)

theorem add_pos_left (a₂) (h : 0 < a₁) : 0 < a₁ + a₂ := by exact ( Nat.lt_of_lt_of_le h (Nat.le_add_right ..))

theorem add_pos_right (a₁) (h : 0 < a₂) : 0 < a₁ + a₂ := by exact ( Nat.lt_of_lt_of_le h (Nat.le_add_left ..))

mutual

partial def ExBase.evalPos (va : ExBase sℕ a) : Option Q(0 < $a) :=
  match va with
  | .atom _ => none
  | .sum va => va.evalPos

partial def ExProd.evalPos (va : ExProd sℕ a) : Option Q(0 < $a) :=
  match va with
  | .const _ _ =>
    have lit : Q(ℕ) := a.appArg!
    haveI : $a =Q Nat.rawCast $lit := ⟨⟩
    haveI p : Nat.ble 1 $lit =Q true := ⟨⟩
    by exact some (q(const_pos $lit $p))
  | .mul (e := ea₁) vxa₁ _ va₂ => do
    let pa₁ ← vxa₁.evalPos
    let pa₂ ← va₂.evalPos
    some q(mul_exp_pos $ea₁ $pa₁ $pa₂)

partial def ExSum.evalPos (va : ExSum sℕ a) : Option Q(0 < $a) :=
  match va with
  | .zero => none
  | .add (a := a₁) (b := a₂) va₁ va₂ => do
    match va₁.evalPos with
    | some p => some q(add_pos_left $a₂ $p)
    | none => let p ← va₂.evalPos; some q(add_pos_right $a₁ $p)

end

theorem pow_one (a : R) : a ^ nat_lit 1 = a := by simp

theorem pow_bit0 (_ : (a : R) ^ k = b) (_ : b * b = c) : a ^ (Nat.mul (nat_lit 2) k) = c := by
  subst_vars; simp [Nat.succ_mul, pow_add]

theorem pow_bit1 (_ : (a : R) ^ k = b) (_ : b * b = c) (_ : c * a = d) :
    a ^ (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1)) = d := by
  subst_vars; simp [Nat.succ_mul, pow_add]

partial def evalPowNat (va : ExSum sα a) (n : Q(ℕ)) : Result (ExSum sα) q($a ^ $n) :=
  let nn := n.natLit!
  if nn = 1 then
    ⟨_, va, (q(pow_one $a) : Expr)⟩
  else
    let nm := nn >>> 1
    have m : Q(ℕ) := mkRawNatLit nm
    if nn &&& 1 = 0 then
      let ⟨_, vb, pb⟩ := evalPowNat va m
      let ⟨_, vc, pc⟩ := evalMul sα vb vb
      ⟨_, vc, (q(pow_bit0 $pb $pc) : Expr)⟩
    else
      let ⟨_, vb, pb⟩ := evalPowNat va m
      let ⟨_, vc, pc⟩ := evalMul sα vb vb
      let ⟨_, vd, pd⟩ := evalMul sα vc va
      ⟨_, vd, (q(pow_bit1 $pb $pc $pd) : Expr)⟩

theorem one_pow (b : ℕ) : ((nat_lit 1).rawCast : R) ^ b = (nat_lit 1).rawCast := by simp

theorem mul_pow (_ : ea₁ * b = c₁) (_ : a₂ ^ b = c₂) :
    (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂ := by subst_vars; simp [_root_.mul_pow, pow_mul]

def evalPowProd (va : ExProd sα a) (vb : ExProd sℕ b) : Result (ExProd sα) q($a ^ $b) :=
  let res : Option (Result (ExProd sα) q($a ^ $b)) := do
    match va, vb with
    | .const 1, _ => some ⟨_, va, (q(one_pow (R := $α) $b) : Expr)⟩
    | .const za ha, .const zb hb =>
      assert! 0 ≤ zb
      let ra := Result.ofRawRat za a ha
      have lit : Q(ℕ) := b.appArg!
      let rb := (q(IsNat.of_raw ℕ $lit) : Expr)
      let rc ← NormNum.evalPow.core q($a ^ $b) q(HPow.hPow) q($a) q($b) lit rb
        q(CommSemiring.toSemiring) ra
      let ⟨zc, hc⟩ ← rc.toRatNZ
      let ⟨c, pc⟩ := rc.toRawEq
      some ⟨c, .const zc hc, pc⟩
    | .mul vxa₁ vea₁ va₂, vb => do
      let ⟨_, vc₁, pc₁⟩ := evalMulProd sℕ vea₁ vb
      let ⟨_, vc₂, pc₂⟩ := evalPowProd va₂ vb
      some ⟨_, .mul vxa₁ vc₁ vc₂, q(mul_pow $pc₁ $pc₂)⟩
    | _, _ => none
  res.getD (evalPowProdAtom sα va vb)

structure ExtractCoeff (e : Q(ℕ)) where
  k : Q(ℕ)
  e' : Q(ℕ)
  ve' : ExProd sℕ e'
  p : Q($e = $e' * $k)

theorem coeff_one (k : ℕ) : k.rawCast = (nat_lit 1).rawCast * k := by simp

theorem coeff_mul (a₁ a₂ : ℕ) (_ : a₃ = c₂ * k) : a₁ ^ a₂ * a₃ = (a₁ ^ a₂ * c₂) * k := by
  subst_vars; rw [mul_assoc]

def extractCoeff (va : ExProd sℕ a) : ExtractCoeff a :=
  match va with
  | .const _ _ =>
    have k : Q(ℕ) := a.appArg!
    ⟨k, q((nat_lit 1).rawCast), .const 1, (q(coeff_one $k) : Expr)⟩
  | .mul (x := a₁) (e := a₂) va₁ va₂ va₃ =>
    let ⟨k, _, vc, pc⟩ := extractCoeff va₃
    ⟨k, _, .mul va₁ va₂ vc, q(coeff_mul $a₁ $a₂ $pc)⟩

theorem pow_one_cast (a : R) : a ^ (nat_lit 1).rawCast = a := by simp

theorem zero_pow (_ : 0 < b) : (0 : R) ^ b = 0 := by exact ( match b with | b+1 => by simp [pow_succ])

theorem single_pow (_ : (a : R) ^ b = c) : (a + 0) ^ b = c + 0 := by simp [*]

