/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelEventualUnits

/-!
# Marked elements and units in an enlarged fixed presentation model

An initial coefficient model can be enlarged to contain finitely many
specified elements, or units, of the original algebra. Keeping the same
presentation permits transport of already descended diagram arrows.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]

/-- Mark finitely many elements while retaining the original coefficient stage. -/
theorem exists_integer_model_marked_extension {K : Type v} [Finite K]
    (x : K → B) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ _h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S,
        ∃ y : K → P.ModelOfHasCoeffs S,
          ∀ k, P.tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ y k) = x k := by
  classical
  obtain ⟨t, ht⟩ := A₀.fg_iff_finiteType.mpr inferInstance
  let q := fun k ↦ P.σ (x k)
  let T : Set A := (s ∪ t) ∪ ⋃ k, (q k).coeffs
  have hT : T.Finite := (hs.union t.finite_toSet).union
    (Set.finite_iUnion fun k ↦ (q k).coeffs.finite_toSet)
  let S := Algebra.adjoin ℤ T
  have h₀ : A₀ ≤ S := by
    rw [← ht, Algebra.adjoin_le_iff]
    exact fun a ha ↦ Algebra.subset_adjoin (Or.inl (Or.inr ha))
  let hP : P.HasCoeffs S := integerModel_hasCoeffs_mono P h₀
  have hq (k) : q k ∈ Set.range (map (algebraMap S A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.mpr ⟨k, ha⟩))⟩, rfl⟩
  choose q₀ hq₀ using hq
  refine ⟨S, Algebra.FiniteType.adjoin_of_finite hT,
    fun a ha ↦ Algebra.subset_adjoin (Or.inl (Or.inl ha)), h₀, hP,
    fun k ↦ Ideal.Quotient.mk _ (q₀ k), fun k ↦ ?_⟩
  rw [P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
    ← MvPolynomial.aeval_map_algebraMap A, hq₀]
  exact P.aeval_val_σ (x k)

/-- Mark finitely many units, constructing their inverses at a later fixed-model stage. -/
theorem exists_integer_model_unit_extension {K : Type v} [Finite K]
    (x : K → Bˣ) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ _h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S,
        ∃ y : K → (P.ModelOfHasCoeffs S)ˣ,
          ∀ k, P.tensorModelOfHasCoeffsEquiv S (1 ⊗ₜ (y k : P.ModelOfHasCoeffs S)) =
            (x k : B) := by
  obtain ⟨R, hR, _, h₀R, hPR, y, hy⟩ :=
    exists_integer_model_marked_extension P A₀ (fun k ↦ (x k : B)) ∅ Set.finite_empty
  let := hR
  let := hPR
  obtain ⟨S, hS, hsS, hRS, hPS, z, hz⟩ :=
    exists_integer_model_eventual_units P R y x hy s hs
  let := hPS
  refine ⟨S, hS, hsS, h₀R.trans hRS, hPS, z, fun k ↦ ?_⟩
  rw [hz, integerModelTransition_recovery, hy]

end FLT.Mazur.Approximation
