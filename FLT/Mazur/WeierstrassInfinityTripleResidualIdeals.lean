/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleDefectReduction

/-!
# Independence of the residual ideal from the output chosen as center

Reciprocity gives explicit ideal membership in both directions without
inverting either leading coefficient. Combined with the quadratic reduction,
this permits comparison in either output's parameters over any quotient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

/-- The nonlinear reciprocity equation identifies the two cross-residual ideals. -/
theorem infinity_residual_span_reciprocity {S : Type*} [CommRing S] (a e f m r : S)
    (h : e + f + a * e * f + r * m = 0) :
    Ideal.span ({e, m} : Set S) = Ideal.span {f, m} := by
  have he : e = -(1 + a * e) * f - r * m := by linear_combination h
  have hf : f = -(1 + a * f) * e - r * m := by linear_combination h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · rw [he]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rcases hx with rfl
      exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · rw [hf]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rcases hx with rfl
      exact Ideal.subset_span (by simp)

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The two output centers generate exactly the same residual ideal, with the minor reoriented. -/
theorem infinityTripleResidual_span_swap (j k : Fin 4) :
    Ideal.span ({infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j,
      infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j)
        (infinityTripleOutputIndex k)} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k,
        infinityTripleNegMinor W hΔ (infinityTripleOutputIndex k)
          (infinityTripleOutputIndex j)} := by
  rw [infinityTripleNegMinor_swap W hΔ (infinityTripleOutputIndex k)
    (infinityTripleOutputIndex j), Ideal.span_pair_neg]
  exact infinity_residual_span_reciprocity _ _ _ _ _
    (infinityTripleNegLineResidual_reciprocity W hΔ j k)

/-- The two finite quadratic presentations agree even when leading coefficients are not units. -/
theorem infinityTripleQuadraticDefect_span_swap (j k : Fin 4) :
    let e := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j
    let f := infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex j) k
    let H := infinityTripleQuadraticDefect W hΔ j k
    let K := infinityTripleQuadraticDefect W hΔ k j
    Ideal.span ({e, H.coeff 0, H.coeff 1} : Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {f, K.coeff 0, K.coeff 1} := by
  dsimp only
  rw [← infinityTripleQuadraticDefect_span_two, ← infinityTripleQuadraticDefect_span_two]
  exact infinityTripleResidual_span_swap W hΔ j k

end FLT.Mazur.WeierstrassIntegralChart
