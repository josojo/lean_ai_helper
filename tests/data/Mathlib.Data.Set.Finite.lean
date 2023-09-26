/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Data.Finite.Basic

#align_import data.set.finite from "leanprover-community/mathlib"@"7fdd4f3746cb059edfdb5d52cba98f66fce418c0"

/-!
# Finite sets

This file defines predicates for finite and infinite sets and provides
`Fintype` instances for many set constructions. It also proves basic facts
about finite sets and gives ways to manipulate `Set.Finite` expressions.

## Main definitions

* `Set.Finite : Set α → Prop`
* `Set.Infinite : Set α → Prop`
* `Set.toFinite` to prove `Set.Finite` for a `Set` from a `Finite` instance.
* `Set.Finite.toFinset` to noncomputably produce a `Finset` from a `Set.Finite` proof.
  (See `Set.toFinset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Fintype` instance.
Since `Set.Finite` is `Prop`-valued, this is the mere fact that the `Fintype` instance
exists.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-- A set is finite if there is a `Finset` with the same elements.
This is represented as there being a `Fintype` instance for the set
coerced to a type.

Note: this is a custom inductive type rather than `Nonempty (Fintype s)`
so that it won't be frozen as a local instance. -/
protected
inductive Finite (s : Set α) : Prop
  | intro : Fintype s → s.Finite
#align set.finite Set.Finite

-- The `protected` attribute does not take effect within the same namespace block.
end Set

namespace Set

theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩
#align set.finite_def Set.finite_def

alias finite_def ↔ Finite.nonempty_fintype _
#align set.finite.nonempty_fintype Set.Finite.nonempty_fintype

theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := by
  rw [finite_iff_nonempty_fintype, finite_def]
#align set.finite_coe_iff Set.finite_coe_iff

/-- Constructor for `Set.Finite` using a `Finite` instance. -/
theorem toFinite (s : Set α) [Finite s] : s.Finite :=
  finite_coe_iff.mp ‹_›
#align set.to_finite Set.toFinite

/-- Construct a `Finite` instance for a `Set` from a `Finset` with the same elements. -/
protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.Finite :=
  ⟨Fintype.ofFinset s H⟩
#align set.finite.of_finset Set.Finite.ofFinset

/-- Projection of `Set.Finite` to its `Finite` instance.
This is intended to be used with dot notation.
See also `Set.Finite.Fintype` and `Set.Finite.nonempty_fintype`. -/
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s :=
  finite_coe_iff.mpr h
#align set.finite.to_subtype Set.Finite.to_subtype

/-- A finite set coerced to a type is a `Fintype`.
This is the `Fintype` projection for a `Set.Finite`.

Note that because `Finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
protected noncomputable def Finite.fintype {s : Set α} (h : s.Finite) : Fintype s :=
  h.nonempty_fintype.some
#align set.finite.fintype Set.Finite.fintype

/-- Using choice, get the `Finset` that represents this `Set`. -/
protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
  @Set.toFinset _ _ h.fintype
#align set.finite.to_finset Set.Finite.toFinset

theorem Finite.toFinset_eq_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset = s.toFinset := by
  -- porting note: was `rw [Finite.toFinset]; congr`
  -- in Lean 4, a goal is left after `congr`
  have : h.fintype = ‹_› := Subsingleton.elim _ _
  rw [Finite.toFinset, this]
#align set.finite.to_finset_eq_to_finset Set.Finite.toFinset_eq_toFinset

@[simp]
theorem toFinite_toFinset (s : Set α) [Fintype s] : s.toFinite.toFinset = s.toFinset :=
  s.toFinite.toFinset_eq_toFinset
#align set.to_finite_to_finset Set.toFinite_toFinset

theorem Finite.exists_finset {s : Set α} (h : s.Finite) :
    ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s := by
  cases h
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩
#align set.finite.exists_finset Set.Finite.exists_finset

theorem Finite.exists_finset_coe {s : Set α} (h : s.Finite) : ∃ s' : Finset α, ↑s' = s := by
  cases h
  exact ⟨s.toFinset, s.coe_toFinset⟩
#align set.finite.exists_finset_coe Set.Finite.exists_finset_coe

/-- Finite sets can be lifted to finsets. -/
instance : CanLift (Set α) (Finset α) (↑) Set.Finite where prf _ hs := hs.exists_finset_coe

/-- A set is infinite if it is not finite.

This is protected so that it does not conflict with global `Infinite`. -/
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite
#align set.infinite Set.Infinite

@[simp]
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  not_not
#align set.not_infinite Set.not_infinite

alias not_infinite ↔ _ Finite.not_infinite
#align set.finite.not_infinite Set.Finite.not_infinite

attribute [simp] Finite.not_infinite

/-- See also `finite_or_infinite`, `fintypeOrInfinite`. -/
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _
#align set.finite_or_infinite Set.finite_or_infinite

protected theorem infinite_or_finite (s : Set α) : s.Infinite ∨ s.Finite :=
  em' _
#align set.infinite_or_finite Set.infinite_or_finite

/-! ### Basic properties of `Set.Finite.toFinset` -/


namespace Finite

variable {s t : Set α} {a : α} {hs : s.Finite} {ht : t.Finite}

@[simp]
protected theorem mem_toFinset (h : s.Finite) : a ∈ h.toFinset ↔ a ∈ s :=
  @mem_toFinset _ _ h.fintype _
#align set.finite.mem_to_finset Set.Finite.mem_toFinset

@[simp]
protected theorem coe_toFinset (h : s.Finite) : (h.toFinset : Set α) = s :=
  @coe_toFinset _ _ h.fintype
#align set.finite.coe_to_finset Set.Finite.coe_toFinset

@[simp]
protected theorem toFinset_nonempty (h : s.Finite) : h.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, Finite.coe_toFinset]
#align set.finite.to_finset_nonempty Set.Finite.toFinset_nonempty

/-- Note that this is an equality of types not holding definitionally. Use wisely. -/
theorem coeSort_toFinset (h : s.Finite) : ↥h.toFinset = ↥s := by
  rw [← Finset.coe_sort_coe _, h.coe_toFinset]
#align set.finite.coe_sort_to_finset Set.Finite.coeSort_toFinset

@[simp]
protected theorem toFinset_inj : hs.toFinset = ht.toFinset ↔ s = t :=
  @toFinset_inj _ _ _ hs.fintype ht.fintype
#align set.finite.to_finset_inj Set.Finite.toFinset_inj

@[simp]
theorem toFinset_subset {t : Finset α} : hs.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]
#align set.finite.to_finset_subset Set.Finite.toFinset_subset

@[simp]
theorem toFinset_ssubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]
#align set.finite.to_finset_ssubset Set.Finite.toFinset_ssubset

@[simp]
theorem subset_toFinset {s : Finset α} : s ⊆ ht.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]
#align set.finite.subset_to_finset Set.Finite.subset_toFinset

@[simp]
theorem ssubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]
#align set.finite.ssubset_to_finset Set.Finite.ssubset_toFinset

@[mono]
protected theorem toFinset_subset_toFinset : hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t := by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]
#align set.finite.to_finset_subset_to_finset Set.Finite.toFinset_subset_toFinset

@[mono]
protected theorem toFinset_ssubset_toFinset : hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]
#align set.finite.to_finset_ssubset_to_finset Set.Finite.toFinset_ssubset_toFinset

alias Finite.toFinset_subset_toFinset ↔ _ toFinset_mono
#align set.finite.to_finset_mono Set.Finite.toFinset_mono

alias Finite.toFinset_ssubset_toFinset ↔ _ toFinset_strictMono
#align set.finite.to_finset_strict_mono Set.Finite.toFinset_strictMono

-- Porting note: attribute [protected] doesn't work
-- attribute [protected] toFinset_mono toFinset_strictMono

-- porting note: `simp` can simplify LHS but then it simplifies something
-- in the generated `Fintype {x | p x}` instance and fails to apply `Set.toFinset_setOf`
@[simp high]
protected theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : { x | p x }.Finite) : h.toFinset = Finset.univ.filter p := by
  ext
  -- porting note: `simp` doesn't use the `simp` lemma `Set.toFinset_setOf` without the `_`
  simp [Set.toFinset_setOf _]
#align set.finite.to_finset_set_of Set.Finite.toFinset_setOf

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t := 
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype