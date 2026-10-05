/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionOpposite

/-!
# A cleared product formula for nodal addition

Multiplying the addition x-coordinate by the first x-coordinate avoids the
cancellation in the usual slope formula. The two cleared slope identities
prove the formula, including the tangent chart. Cancelling a common depth
then isolates the depth difference.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

/-- A product formula deduced from the line and second slope identities. -/
theorem node_addX_product_of_identities {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (x y z t l : R)
    (hline : (x - z) * l = y - t)
    (hsecond : (y + t + W.a₁ * z + W.a₃) * l =
      x ^ 2 + x * z + z ^ 2 + W.a₂ * (x + z) + W.a₄ - W.a₁ * y) :
    x * W.toAffine.addX x z l =
      z ^ 2 + (W.a₂ + l ^ 2) * z + W.a₄ - (2 * l + W.a₁) * t - W.a₃ * l := by
  simp only [Affine.addX]
  linear_combination (l + W.a₁) * hline + hsecond

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- The product identity for an actual integral slope on the generic curve. -/
theorem node_addX_product (x y z t l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation (x : K) (y : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation (z : K) (t : K))
    (hxy : ¬ ((x : K) = (z : K) ∧ (y : K) =
      (W.map (algebraMap A K)).toAffine.negY (z : K) (t : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope (x : K) (z : K)
      (y : K) (t : K) = (l : K)) :
    x * W.toAffine.addX x z l =
      z ^ 2 + (W.a₂ + l ^ 2) * z + W.a₄ - (2 * l + W.a₁) * t - W.a₃ * l := by
  obtain ⟨he, hf⟩ := slope_cleared_identities _ h₁ h₂ hxy
  rw [hl] at he hf
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.algebraMap_apply] at hf
  exact node_addX_product_of_identities W x y z t l (by exact_mod_cast he) (by exact_mod_cast hf)

omit [DecidableEq K] in
/-- Cancel the shallower scale in the product formula without dividing by x₂. -/
theorem node_addX_product_scaled {π : A} (hπ : π ≠ 0) (k j : ℕ)
    (a c d l e₃ e₄ : A) (h3 : W.a₃ = π ^ (k + j) * e₃)
    (h4 : W.a₄ = π ^ (k + j) * e₄)
    (hx : (π ^ k * a) * W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l =
      (π ^ (k + j) * c) ^ 2 + (W.a₂ + l ^ 2) * (π ^ (k + j) * c) + W.a₄ -
        (2 * l + W.a₁) * (π ^ (k + j) * d) - W.a₃ * l) :
    a * W.toAffine.addX (π ^ k * a) (π ^ (k + j) * c) l =
      π ^ j * (π ^ (k + j) * c ^ 2 + (W.a₂ + l ^ 2) * c + e₄ -
        (2 * l + W.a₁) * d - e₃ * l) := by
  apply mul_left_cancel₀ (pow_ne_zero k hπ)
  rw [h3, h4] at hx
  simp only [pow_add] at hx ⊢
  linear_combination hx

end FLT.Mazur
