/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteAlgebraComponents
public import Mathlib.RingTheory.Localization.Away.Lemmas

/-! # The local factors form a finite principal cover -/

@[expose] public noncomputable section

namespace FiniteAlgebra

variable (A : Type*) [CommRing A] [IsArtinianRing A]

/-- The factor is the principal localization at its primitive idempotent. -/
instance component_isLocalizationAway (m : ComponentIndex A) :
    IsLocalization.Away (componentIdempotent A m) (Component A m) :=
  IsLocalization.Away.quotient_of_isIdempotentElem (componentIdempotent_isIdempotent A m)

/-- There are only finitely many principal component charts. -/
instance componentIndex_finite : Finite (ComponentIndex A) :=
  inferInstanceAs (Finite (MaximalSpectrum _))

/-- The principal component chart elements generate the unit ideal. -/
theorem span_componentIdempotents_eq_top : Ideal.span (Set.range (componentIdempotent A)) = ⊤ := by
  classical
  let : Fintype (ComponentIndex A) := Fintype.ofFinite _
  apply Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
  have h := (ThreeAdicPlan.componentIdempotent_complete (⊥ : Ideal A)).complete
  change ∑ m, componentIdempotent A m = 1 at h
  rw [← h]
  exact Submodule.sum_mem _ fun m _ ↦ Ideal.subset_span ⟨m, rfl⟩

/-- Every prime of the original algebra belongs to at least one principal component chart. -/
theorem exists_componentIdempotent_notMem (q : Ideal A) [q.IsPrime] :
    ∃ m : ComponentIndex A, componentIdempotent A m ∉ q := by
  by_contra! h
  have hle : Ideal.span (Set.range (componentIdempotent A)) ≤ q :=
    Ideal.span_le.mpr (by rintro _ ⟨m, rfl⟩; exact h m)
  rw [span_componentIdempotents_eq_top] at hle
  exact Ideal.IsPrime.ne_top' (top_le_iff.mp hle)

end FiniteAlgebra
