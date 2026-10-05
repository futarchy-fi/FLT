/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSecantSlope
public import FLT.Mazur.EllipticReductionRelation

/-!
# Addition with an integral nodal tangent slope

The actual addition formulas show that two points reducing to the node have
sum reducing to the node whenever the integral secant slope reduces to a nodal
tangent. This permits singular reduced points throughout the calculation.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- An integral nodal tangent slope makes both addition coordinates vanish in the residue field. -/
theorem node_add_coordinates_mem {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {x₁ y₁ x₂ l : R}
    (h2 : W.a₂ ∈ maximalIdeal R) (h3 : W.a₃ ∈ maximalIdeal R)
    (hx₁ : x₁ ∈ maximalIdeal R) (hy₁ : y₁ ∈ maximalIdeal R) (hx₂ : x₂ ∈ maximalIdeal R)
    (hl : residue R l = 0 ∨ residue R l = -residue R W.a₁) :
    W.toAffine.addX x₁ x₂ l ∈ maximalIdeal R ∧
      W.toAffine.addY x₁ x₂ y₁ l ∈ maximalIdeal R := by
  have h20 := (residue_eq_zero_iff _).mpr h2
  have h30 := (residue_eq_zero_iff _).mpr h3
  have hx10 := (residue_eq_zero_iff _).mpr hx₁
  have hy10 := (residue_eq_zero_iff _).mpr hy₁
  have hx20 := (residue_eq_zero_iff _).mpr hx₂
  have hx : residue R (W.toAffine.addX x₁ x₂ l) = 0 := by
    simp only [Affine.addX, map_sub, map_add, map_pow, map_mul, h20, hx10, hx20, sub_zero]
    rcases hl with h | h <;> rw [h] <;> ring
  refine ⟨(residue_eq_zero_iff _).mp hx, (residue_eq_zero_iff _).mp ?_⟩
  simp only [Affine.addY, Affine.negY, Affine.negAddY, map_sub, map_neg, map_add, map_mul,
    hx, hx10, hy10, h30, sub_zero, neg_zero, mul_zero, add_zero]

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Actual addition at an integral nodal tangent slope has singular reduction. -/
theorem not_smoothReduction_add_of_node_slope (x₁ y₁ x₂ y₂ l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₁ : K) (y₁ : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Nonsingular (x₂ : K) (y₂ : K))
    (hxy : ¬ ((x₁ : K) = (x₂ : K) ∧ (y₁ : K) =
      (W.map (algebraMap A K)).toAffine.negY (x₂ : K) (y₂ : K)))
    (hs : (W.map (algebraMap A K)).toAffine.slope (x₁ : K) (x₂ : K)
      (y₁ : K) (y₂ : K) = (l : K))
    (h2 : W.a₂ ∈ maximalIdeal A) (h3 : W.a₃ ∈ maximalIdeal A)
    (h4 : W.a₄ ∈ maximalIdeal A) (h6 : W.a₆ ∈ maximalIdeal A)
    (hx₁ : x₁ ∈ maximalIdeal A) (hy₁ : y₁ ∈ maximalIdeal A) (hx₂ : x₂ ∈ maximalIdeal A)
    (hl : residue A l = 0 ∨ residue A l = -residue A W.a₁) :
    ¬ SmoothReduction A W (Affine.Point.toProjective (.some _ _ h₁ + .some _ _ h₂)) := by
  obtain ⟨hx0, hy0⟩ := node_add_coordinates_mem W h2 h3 hx₁ hy₁ hx₂ hl
  rw [Affine.Point.add_some hxy]
  simp only [hs]
  have hx := W.toAffine.map_addX (algebraMap A K) x₁ x₂ l
  have hy := W.toAffine.map_addY (algebraMap A K) x₁ y₁ x₂ l
  change (W.map (algebraMap A K)).toAffine.addX _ _ _ = _ at hx
  change (W.map (algebraMap A K)).toAffine.addY _ _ _ _ = _ at hy
  simp only [ValuationSubring.algebraMap_apply] at hx hy
  simp only [hx, hy]
  rw [smoothReduction_affine_iff]
  have hz3 := (residue_eq_zero_iff _).mpr h3
  have hz4 := (residue_eq_zero_iff _).mpr h4
  have hz6 := (residue_eq_zero_iff _).mpr h6
  intro hn
  have hc := (normalized_nonsingular_iff (W.map (residue A))
    (by simpa using hz3) (by simpa using hz4) (by simpa using hz6) hn.1).mp hn
  exact hc ⟨(residue_eq_zero_iff _).mpr hx0, (residue_eq_zero_iff _).mpr hy0⟩

end FLT.Mazur
