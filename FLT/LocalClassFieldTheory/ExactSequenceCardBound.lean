/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteHomologyCard

/-!
# The cardinal bound for relative-order induction

An exact sequence A → B → C with finite outer terms has finite middle term
of order at most |A| |C|. The arithmetic inflation-restriction sequence must
still be supplied by a proof of exactness.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable {R : Type} [Ring R] (S : ShortComplex (ModuleCat R))
  [Finite S.X₁] [Finite S.X₃]

/-- Exactness and finite outer modules imply finiteness of the middle module. -/
theorem exactSequence_middle_finite (hS : S.Exact) : Finite S.X₂ := by
  let : Finite S.g.hom.ker := by
    rw [← hS.moduleCat_range_eq_ker]
    exact Finite.of_surjective S.f.hom.rangeRestrict (fun ⟨y, x, h⟩ => ⟨x, Subtype.ext h⟩)
  let : Finite (S.X₂ ⧸ S.g.hom.ker) :=
    Finite.of_equiv S.g.hom.range S.g.hom.quotKerEquivRange.toEquiv.symm
  exact Finite.of_equiv ((S.X₂ ⧸ S.g.hom.ker) × S.g.hom.ker)
    AddSubgroup.addGroupEquivQuotientProdAddSubgroup.symm

/-- The exact middle order is bounded by the product of the two outer orders. -/
theorem exactSequence_card_le (hS : S.Exact) :
    Nat.card S.X₂ ≤ Nat.card S.X₁ * Nat.card S.X₃ := by
  rw [linearMap_card_eq_ker_mul_range S.g.hom, ← hS.moduleCat_range_eq_ker]
  exact Nat.mul_le_mul
    (Nat.card_le_card_of_surjective S.f.hom.rangeRestrict (fun ⟨y, x, h⟩ => ⟨x, Subtype.ext h⟩))
    (Nat.card_le_card_of_injective _ Subtype.val_injective)

end LocalClassFieldTheory
