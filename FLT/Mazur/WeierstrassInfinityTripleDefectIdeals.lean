/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleDefectCoefficients
public import Mathlib.RingTheory.Ideal.Span

/-!
# Equality of the residual ideal and the quadratic coefficient ideal

The coefficient formulas give one inclusion. The explicit weighted certificate
and the genuine scale unit give the other. Consequently the two presentations
remain equivalent modulo every ideal, including nonreduced quotients.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Every defect coefficient belongs to any ideal containing both actual residuals. -/
theorem infinityTripleQuadraticDefect_coeff_mem (j k : Fin 4)
    (I : Ideal Γ(InfinityTripleFull W hΔ, ⊤))
    (he : infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j ∈ I)
    (hm : infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k) ∈ I) (i : ℕ) :
    (infinityTripleQuadraticDefect W hΔ j k).coeff i ∈ I := by
  rw [infinityTripleQuadraticDefect_coeff]
  exact I.sub_mem (I.mul_mem_right _ he) (I.mul_mem_right _ hm)

/-- The scale-unit certificate recovers minor membership from the three defect coefficients. -/
theorem infinityTripleQuadraticDefect_minor_mem (j k : Fin 4)
    (I : Ideal Γ(InfinityTripleFull W hΔ, ⊤))
    (he : infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j ∈ I)
    (hh : ∀ i : Fin 3, (infinityTripleQuadraticDefect W hΔ j k).coeff i ∈ I) :
    infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k) ∈ I := by
  apply (I.mul_unit_mem_iff_mem (infinityTripleScalar_scale_unit W hΔ j)).mp
  rw [infinityTripleQuadraticDefect_minor_certificate]
  apply I.add_mem
  · exact I.sub_mem (I.add_mem (I.mul_mem_right _ he) (I.mul_mem_left _ (hh 0)))
      (I.mul_mem_left _ (hh 1))
  · apply I.mul_mem_left
    exact I.add_mem (I.sub_mem (I.mul_mem_left _ (hh 0)) (I.mul_mem_left _ (hh 1)))
      (I.mul_mem_left _ (hh 2))

/-- The residual pair and the residual plus three quadratic coefficients generate one ideal. -/
theorem infinityTripleQuadraticDefect_span (j k : Fin 4) :
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let m := infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
      (infinityTripleOutputIndex k)
    let H := infinityTripleQuadraticDefect W hΔ j k
    Ideal.span ({e, m} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span (insert e (Set.range fun i : Fin 3 => H.coeff i)) := by
  dsimp only
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ha
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · rcases ha with rfl
      apply infinityTripleQuadraticDefect_minor_mem W hΔ j k
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · intro i
        exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨i, rfl⟩
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · apply infinityTripleQuadraticDefect_coeff_mem W hΔ j k
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

end FLT.Mazur.WeierstrassIntegralChart
