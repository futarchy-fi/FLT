/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantFormula

/-!
# The product identity for divided secants

Vieta's constant-term identity is valid before cancelling the input scale.
It expresses the output abscissa through the line intercept, allowing a
second division on same-branch unequal-depth inputs.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 b4 b6 x y u v l : R)

/-- The two divided line relations give the product of the three abscissae. -/
theorem divided_addX_product
    (he : y ^ 2 + (W.a₁ * x + b3) * y =
      s * x ^ 3 + W.a₂ * x ^ 2 + b4 * x + b6)
    (hl : l * (x - u) = y - v)
    (hc : l * (y + v + W.a₁ * u + b3) =
      s * (x ^ 2 + x * u + u ^ 2) + W.a₂ * (x + u) + b4 - W.a₁ * y) :
    x * u * W.toAffine.addX (s * x) (s * u) l =
      (y - l * x) ^ 2 + b3 * (y - l * x) - b6 := by
  simp only [Affine.addX]
  linear_combination -he + x * hc - x * l * hl

/-- A genuine divided secant satisfies the product identity over any coefficient ring. -/
theorem divided_secant_product
    (h₁ : y ^ 2 + (W.a₁ * x + b3) * y =
      s * x ^ 3 + W.a₂ * x ^ 2 + b4 * x + b6)
    (h₂ : v ^ 2 + (W.a₁ * u + b3) * v =
      s * u ^ 3 + W.a₂ * u ^ 2 + b4 * u + b6)
    (hu : IsUnit (x - u)) (hl : l * (x - u) = y - v) :
    x * u * W.toAffine.addX (s * x) (s * u) l =
      (y - l * x) ^ 2 + b3 * (y - l * x) - b6 :=
  divided_addX_product W s b3 b4 b6 x y u v l h₁ hl
    (divided_secant_relation W s b3 b4 b6 h₁ h₂ hu hl)

end FLT.Mazur.WeierstrassDilatation
