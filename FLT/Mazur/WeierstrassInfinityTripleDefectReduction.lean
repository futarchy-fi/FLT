/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleDefectIdeals

/-!
# Two quadratic coefficients suffice for the associativity obstruction

The highest defect coefficient is already a multiple of the first residual.
The residual ideal therefore needs only that residual and the constant and
linear defect coefficients. This is an equality of ideals, not only radicals.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The top quadratic discrepancy is already a multiple of the first cross residual. -/
theorem infinityTripleQuadraticDefect_coeff_two (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    (infinityTripleQuadraticDefect W hΔ j k).coeff 2 =
      infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j *
        (A.a₃ * (infinityTripleParamInputPair W hΔ j k).coeff 2) := by
  have h := infinityTripleParam_residual_coeff_top W hΔ j k
  dsimp only at h ⊢
  simp only [infinityTripleQuadraticDefect, coeff_sub, coeff_C_mul]
  linear_combination h

/-- Modulo any ideal containing the first residual, only two coefficients need checking. -/
theorem infinityTripleQuadraticDefect_minor_mem_iff (j k : Fin 4)
    (I : Ideal Γ(InfinityTripleFull W hΔ, ⊤))
    (he : infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j ∈ I) :
    infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
        (infinityTripleOutputIndex k) ∈ I ↔
      (infinityTripleQuadraticDefect W hΔ j k).coeff 0 ∈ I ∧
        (infinityTripleQuadraticDefect W hΔ j k).coeff 1 ∈ I := by
  constructor
  · intro hm
    exact ⟨infinityTripleQuadraticDefect_coeff_mem W hΔ j k I he hm 0,
      infinityTripleQuadraticDefect_coeff_mem W hΔ j k I he hm 1⟩
  · rintro ⟨h₀, h₁⟩
    apply infinityTripleQuadraticDefect_minor_mem W hΔ j k I he
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · rw [infinityTripleQuadraticDefect_coeff_two]
      exact I.mul_mem_right _ he

/-- A three-generator presentation of the actual two-residual ideal. -/
theorem infinityTripleQuadraticDefect_span_two (j k : Fin 4) :
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    let H := infinityTripleQuadraticDefect W hΔ j k
    Ideal.span ({e, m} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {e, H.coeff 0, H.coeff 1} := by
  dsimp only
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ha
    · exact Ideal.subset_span (by simp)
    · rcases ha with rfl
      apply (infinityTripleQuadraticDefect_minor_mem_iff W hΔ j k _
        (Ideal.subset_span (by simp))).mpr
      exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  · apply Ideal.span_le.mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Ideal.subset_span (by simp)
    all_goals
      apply infinityTripleQuadraticDefect_coeff_mem W hΔ j k
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)

/-- The full member's associativity is exactly one residual and two explicit scalar coefficients. -/
theorem infinityTripleFull_assoc_iff_quadratic_coefficients :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
        infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ ↔
      infinityTripleNegLineResidual W hΔ 6 2 = 0 ∧
        (infinityTripleQuadraticDefect W hΔ 2 3).coeff 0 = 0 ∧
          (infinityTripleQuadraticDefect W hΔ 2 3).coeff 1 = 0 := by
  rw [infinityTripleFull_assoc_iff_line_residual]
  constructor
  · rintro ⟨he, hm⟩
    have h := infinityTripleQuadraticDefect_eq_zero W hΔ 2 3 he hm
    exact ⟨he, by rw [h, coeff_zero], by rw [h, coeff_zero]⟩
  · rintro ⟨he, h₀, h₁⟩
    refine ⟨he, ?_⟩
    have h := (infinityTripleQuadraticDefect_minor_mem_iff W hΔ 2 3 ⊥
      (by change infinityTripleNegLineResidual W hΔ 6 2 = 0; exact he)).mpr
        ⟨by simpa only [Ideal.mem_bot] using h₀, by simpa only [Ideal.mem_bot] using h₁⟩
    exact h

end FLT.Mazur.WeierstrassIntegralChart
