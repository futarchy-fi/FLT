/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization

/-!
# Exact errors in the ordinary conormal characters

The two branch characters differ from the actual addition output by explicit
quadratic and coefficient terms. These identities retain the integral equation.
-/

@[expose] public section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassCurve
variable {S : Type*} [CommRing S] (W : WeierstrassCurve S)
  (u v x y l : S)
local notation "X" => W.toAffine.addX u x l
local notation "Y" => W.toAffine.addY u x v l

/-- The integral first branch character has an explicit quadratic error. -/
theorem ordinaryConormalPolynomial_first
    (hline : l * (u - x) = v - y)
    (hcubic : l * (v + y + W.a₁ * x + W.a₃) =
      u ^ 2 + u * x + x ^ 2 + W.a₂ * (u + x) + W.a₄ - W.a₁ * v) :
    l * Y - (l + W.a₁) * y =
      -(X ^ 2 + x * X + x ^ 2 + W.a₂ * (X + x) + W.a₄) := by
  dsimp only [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, toAffine]
  linear_combination -W.a₁ * hline - hcubic

/-- The opposite branch has the same error and the retained third coefficient term. -/
theorem ordinaryConormalPolynomial_second
    (hline : l * (u - x) = v - y)
    (hcubic : l * (v + y + W.a₁ * x + W.a₃) =
      u ^ 2 + u * x + x ^ 2 + W.a₂ * (u + x) + W.a₄ - W.a₁ * v) :
    (l + W.a₁) * (Y + W.a₁ * X) - l * (y + W.a₁ * x) =
      -(X ^ 2 + x * X + x ^ 2 + W.a₂ * (X + x) + W.a₄ + W.a₁ * W.a₃) := by
  have h := ordinaryConormalPolynomial_first W u v x y l hline hcubic
  dsimp only [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, toAffine] at *
  linear_combination h + W.a₁ * hline

end FLT.Mazur.WeierstrassIntegralChart
