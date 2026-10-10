/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleResidualIdeals

/-!
# The residual ideal is the normalized coordinate difference ideal

The actual own-line relation gives a determinant-one matrix taking normalized
coordinate differences to the residual and minor. This identifies the exact
ideals over nonreduced rings, and links the quadratic certificates to the
original coordinate comparison without a radical or localization step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

/-- A determinant-one change of two generators preserves their exact ideal. -/
theorem infinity_span_pair_determinant_one {S : Type*} [CommRing S]
    (a b c d x y : S) (hd : a * d - b * c = 1) :
    Ideal.span ({a * x + b * y, c * x + d * y} : Set S) = Ideal.span {x, y} := by
  have hx : x = d * (a * x + b * y) - b * (c * x + d * y) := by
    linear_combination -x * hd
  have hy : y = a * (c * x + d * y) - c * (a * x + b * y) := by
    linear_combination -y * hd
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    all_goals
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have hm : d * (a * x + b * y) - b * (c * x + d * y) ∈
          Ideal.span ({a * x + b * y, c * x + d * y} : Set S) :=
        Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      rwa [← hx] at hm
    · rw [hz]
      have hm : a * (c * x + d * y) - c * (a * x + b * y) ∈
          Ideal.span ({a * x + b * y, c * x + d * y} : Set S) :=
        Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      rwa [← hy] at hm

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The matrix from coordinate differences to the residual and minor has determinant one. -/
theorem infinityTripleResidual_coordinate_determinant (j : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let b := infinityTripleLineIntercept W hΔ j
    let m := infinityTripleScalarSlope W hΔ j
    let x := infinityTripleScalarX W hΔ (infinityTripleOutputIndex j)
    let z := infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j)
    (A.a₁ * b - m) * (A.a₃ * x) - (1 + A.a₃ * b) * (-(1 + A.a₃ * z)) = 1 := by
  have h := infinityTripleNegLineResidual_output W hΔ j
  dsimp only [infinityTripleNegLineResidual, infinityTripleNegY] at h ⊢
  linear_combination (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))).a₃ * h

/-- The actual residual and minor are explicit linear combinations of coordinate differences. -/
theorem infinityTripleResidual_coordinate_expansion (i : Fin 7) (j : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let b := infinityTripleLineIntercept W hΔ j
    let m := infinityTripleScalarSlope W hΔ j
    let x := infinityTripleScalarX W hΔ (infinityTripleOutputIndex j)
    let z := infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j)
    let dx := infinityTripleScalarX W hΔ i - x
    let dz := infinityTripleScalarZ W hΔ i - z
    infinityTripleNegLineResidual W hΔ i j = (A.a₁ * b - m) * dx + (1 + A.a₃ * b) * dz ∧
      infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i =
        -(1 + A.a₃ * z) * dx + (A.a₃ * x) * dz := by
  have h := infinityTripleNegLineResidual_output W hΔ j
  dsimp only [infinityTripleNegLineResidual, infinityTripleNegMinor, infinityTripleNegY] at h ⊢
  constructor
  · linear_combination h
  · ring

/-- The exact obstruction ideal is the ideal of the two normalized coordinate differences. -/
theorem infinityTripleResidual_coordinate_span (i : Fin 7) (j : Fin 4) :
    Ideal.span ({infinityTripleNegLineResidual W hΔ i j,
      infinityTripleNegMinor W hΔ (infinityTripleOutputIndex j) i} :
        Set Γ(InfinityTripleFull W hΔ, ⊤)) =
      Ideal.span {infinityTripleScalarX W hΔ i -
        infinityTripleScalarX W hΔ (infinityTripleOutputIndex j),
        infinityTripleScalarZ W hΔ i -
          infinityTripleScalarZ W hΔ (infinityTripleOutputIndex j)} := by
  rw [(infinityTripleResidual_coordinate_expansion W hΔ i j).1,
    (infinityTripleResidual_coordinate_expansion W hΔ i j).2]
  exact infinity_span_pair_determinant_one _ _ _ _ _ _
    (infinityTripleResidual_coordinate_determinant W hΔ j)

end FLT.Mazur.WeierstrassIntegralChart
