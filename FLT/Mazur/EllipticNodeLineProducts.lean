/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeAdditionProduct

/-!
# Products of the three line-intersection coordinates

The two slope identities give the pairwise-product coefficient. The curve
equation gives the product coefficient. These are polynomial identities and
apply to secants and tangents without a separability hypothesis.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Pairwise products of the three intersection x-coordinates recover the line intercept. -/
theorem node_line_pair_products (x y z t l : R)
    (hline : (x - z) * l = y - t)
    (hsecond : (y + t + W.a₁ * z + W.a₃) * l =
      x ^ 2 + x * z + z ^ 2 + W.a₂ * (x + z) + W.a₄ - W.a₁ * y) :
    x * z + x * W.toAffine.addX x z l + z * W.toAffine.addX x z l =
      W.a₄ - (2 * l + W.a₁) * (y - l * x) - W.a₃ * l := by
  simp only [Affine.addX]
  linear_combination hsecond - l * hline

/-- The triple product recovers a₆ up to the square and a₃-multiple of the intercept. -/
theorem node_line_triple_product (x y z t l : R)
    (he : W.toAffine.Equation z t)
    (hline : (x - z) * l = y - t)
    (hsecond : (y + t + W.a₁ * z + W.a₃) * l =
      x ^ 2 + x * z + z ^ 2 + W.a₂ * (x + z) + W.a₄ - W.a₁ * y) :
    x * z * W.toAffine.addX x z l =
      (y - l * x) ^ 2 + W.a₃ * (y - l * x) - W.a₆ := by
  have hp := node_addX_product_of_identities W x y z t l hline hsecond
  have heq := (Affine.equation_iff _ _).mp he
  have hn : y - l * x = t - l * z := by linear_combination -hline
  rw [hn]
  linear_combination z * hp - heq

end FLT.Mazur
