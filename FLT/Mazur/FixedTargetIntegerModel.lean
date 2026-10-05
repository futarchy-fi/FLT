/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelTransition

/-!
# Lifting maps while retaining a fixed target presentation

A map from a finite-type integer algebra lifts to an enlargement of any
specified coefficient stage of the target presentation. The target model
is not replaced by a new unrelated presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Lift a map from a finite-type integer algebra to a larger stage of a
fixed target presentation, including any requested finite base coefficients. -/
theorem exists_fixed_target_integer_model_hom {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [Algebra.FiniteType ℤ C] (φ : C →+* B) (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧ A₀ ≤ A₁ ∧
      ∃ _hP : P.HasCoeffs A₁, ∃ φ₁ : C →+* P.ModelOfHasCoeffs A₁,
        ∀ c, P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ φ₁ c) = φ c := by
  classical
  let : Algebra.FinitePresentation ℤ C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let Q := Algebra.Presentation.ofFinitePresentation ℤ C
  let p := fun i ↦ P.σ (φ (Q.val i))
  have hp (i) : aeval P.val (p i) = φ (Q.val i) := P.aeval_val_σ _
  let q := fun j ↦ aeval p (Q.relation j)
  have hq (j) : aeval P.val (q j) = 0 := by
    change ((aeval P.val).restrictScalars ℤ) (aeval p (Q.relation j)) = 0
    rw [comp_aeval_apply]
    simp only [AlgHom.restrictScalars_apply, hp]
    change aeval (fun i ↦ φ.toIntAlgHom (Q.val i)) (Q.relation j) = 0
    rw [← comp_aeval_apply, Q.aeval_val_relation, map_zero]
  obtain ⟨t, ht⟩ := A₀.fg_iff_finiteType.mpr inferInstance
  let S : Set A := (s ∪ t) ∪ ⋃ i, (p i).coeffs
  have hS : S.Finite := (hs.union t.finite_toSet).union
    (Set.finite_iUnion fun i ↦ (p i).coeffs.finite_toSet)
  obtain ⟨A₁, hA₁, hS₁, hP₁, q₁, hq₁, hz⟩ :=
    exists_integer_model_relations P q hq S hS
  let := hP₁
  have hinc : A₀ ≤ A₁ := by
    rw [← ht, Algebra.adjoin_le_iff]
    exact fun a ha ↦ hS₁ (Or.inl (Or.inr ha))
  have hl (i) : p i ∈ Set.range (map (algebraMap A₁ A)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    exact ⟨⟨a, hS₁ (Or.inr (Set.mem_iUnion.mpr ⟨i, ha⟩))⟩, rfl⟩
  choose p₁ hp₁ using hl
  let π := Ideal.Quotient.mkₐ A₁ (Ideal.span (Set.range (P.relationOfHasCoeffs A₁)))
  let x₁ := fun i ↦ π (p₁ i)
  have hr (j) : aeval x₁ (Q.relation j) = 0 := by
    have heq : aeval p₁ (Q.relation j) = q₁ j := by
      apply MvPolynomial.map_injective (f := algebraMap A₁ A) Subtype.val_injective
      change (map (algebraMap A₁ A)).toIntAlgHom (aeval p₁ (Q.relation j)) = _
      rw [comp_aeval_apply]
      simpa only [RingHom.toIntAlgHom_apply, hp₁] using (hq₁ j).symm
    change aeval (fun i ↦ (π.restrictScalars ℤ) (p₁ i)) (Q.relation j) = 0
    rw [← comp_aeval_apply, heq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hz j)
  have hker : Q.ker ≤ RingHom.ker (aeval x₁) := by
    rw [← Q.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hr j
  let φ₁ := (Ideal.Quotient.liftₐ Q.ker (aeval x₁) hker).comp
    (Q.quotientEquiv.restrictScalars ℤ).symm.toAlgHom
  have hφ (p : Q.Ring) : φ₁ (aeval Q.val p) = aeval x₁ p := by
    rw [← Q.algebraMap_apply, ← Q.quotientEquiv_mk]
    change (Ideal.Quotient.liftₐ Q.ker (aeval x₁) hker)
      ((Q.quotientEquiv.restrictScalars ℤ).symm
        ((Q.quotientEquiv.restrictScalars ℤ) (Ideal.Quotient.mk _ p))) = _
    rw [AlgEquiv.symm_apply_apply]
    rfl
  let g := ((P.tensorModelOfHasCoeffsEquiv A₁).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom).toIntAlgHom
  have hg (i) : g (x₁ i) = φ (Q.val i) := by
    change P.tensorModelOfHasCoeffsEquiv A₁ (1 ⊗ₜ Ideal.Quotient.mk _ (p₁ i)) = _
    rw [P.tensorModelOfHasCoeffsEquiv_tmul, map_one, one_mul,
      ← MvPolynomial.aeval_map_algebraMap A, hp₁]
    exact hp i
  refine ⟨A₁, hA₁, fun a ha ↦ hS₁ (Or.inl (Or.inl ha)), hinc, hP₁, φ₁.toRingHom, ?_⟩
  intro c
  change g (φ₁ c) = φ.toIntAlgHom c
  rw [← Q.aeval_val_σ c, hφ, comp_aeval_apply, comp_aeval_apply]
  simp only [hg, RingHom.toIntAlgHom_apply]

end FLT.Mazur.Approximation
