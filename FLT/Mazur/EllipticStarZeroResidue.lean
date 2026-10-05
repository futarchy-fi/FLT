/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIVCoordinates

/-!
# The residual cubic for the normalized I₀* branch

When a₃,a₄ have depth two and a₆ has depth three, points above the cusp
have y-coordinate in the square of the maximal ideal. Dividing x by π and
y by π² leaves a cubic equation for the residual x-coordinate.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R)

/-- The first divided y-coordinate vanishes in the deeper additive branch. -/
theorem starZero_divided_y_mem {π : R} (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal R)
    (x y e3 e4 e6 : R) (h1 : W.a₁ ∈ maximalIdeal R) (h2 : W.a₂ ∈ maximalIdeal R)
    (h3 : W.a₃ = π ^ 2 * e3) (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6)
    (he : W.toAffine.Equation (π * x) (π * y)) : y ∈ maximalIdeal R := by
  have h := typeIV_scaled_residue W hπ hπm x y (π * e3) (π * e4) (π * e6) h1 h2
    ((maximalIdeal R).mul_mem_right _ hπm)
    (by rw [h3]; ring) (by rw [h4]; ring) (by rw [h6]; ring) he
  have hy : residue R y ^ 2 = 0 := by
    simpa [(residue_eq_zero_iff _).mpr hπm] using h
  exact (residue_eq_zero_iff _).mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp hy)

omit [IsLocalRing R] in
/-- Divide the actual Weierstrass equation by π³ in the I₀* chart. -/
theorem starZero_scaled_equation {π : R} (hπ : π ≠ 0) (x y e2 e3 e4 e6 : R)
    (h2 : W.a₂ = π * e2) (h3 : W.a₃ = π ^ 2 * e3)
    (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6)
    (he : W.toAffine.Equation (π * x) (π ^ 2 * y)) :
    π * y ^ 2 + W.a₁ * x * y + π * e3 * y = x ^ 3 + e2 * x ^ 2 + e4 * x + e6 := by
  apply mul_left_cancel₀ (pow_ne_zero 3 hπ)
  have he' := (Affine.equation_iff _ _).mp he
  rw [h2, h3, h4, h6] at he'
  linear_combination he'

/-- The divided x-coordinate is a root of the I₀* residual cubic. -/
theorem starZero_scaled_residue {π : R} (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal R)
    (x y e2 e3 e4 e6 : R) (h1 : W.a₁ ∈ maximalIdeal R)
    (h2 : W.a₂ = π * e2) (h3 : W.a₃ = π ^ 2 * e3)
    (h4 : W.a₄ = π ^ 2 * e4) (h6 : W.a₆ = π ^ 3 * e6)
    (he : W.toAffine.Equation (π * x) (π ^ 2 * y)) :
    residue R x ^ 3 + residue R e2 * residue R x ^ 2 +
      residue R e4 * residue R x + residue R e6 = 0 := by
  have h := congrArg (residue R) (starZero_scaled_equation W hπ x y e2 e3 e4 e6
    h2 h3 h4 h6 he)
  simpa [(residue_eq_zero_iff _).mpr hπm, (residue_eq_zero_iff _).mpr h1] using h.symm

end FLT.Mazur
