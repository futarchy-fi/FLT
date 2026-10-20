/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentLowerFormula

/-!
# The equation in the smaller output chart

The actual tangent sum and regularity of the output scale prove the equation
in any supplied target datum. The input and output depths need not coincide.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t w b3 b4 b6 a2 b4' b6' e3 e4 e6 u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "l" => tangentLowerSlope W w b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentLowerX W t w a2 u₁ u₂ l
local notation "Y" => tangentLowerY W s t w b3 a2 u₁ u₂ v₁ l

/-- The explicitly divided output satisfies the actual target equation. -/
theorem tangentLower_equation (ht : IsRegular t)
    (hs : s = t * w) (h2 : W.a₂ = t * a2)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (h4' : b4 = t * b4') (h6' : b6 = t * b6')
    (he3 : W.a₃ = t * e3) (he4 : W.a₄ = t * e4) (he6 : W.a₆ = t ^ 2 * e6)
    (h₁ : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (h₂ : v₂ ^ 2 + (W.a₁ * u₂ + b3) * v₂ =
      s * u₂ ^ 3 + W.a₂ * u₂ ^ 2 + b4 * u₂ + b6) :
    Y ^ 2 + (W.a₁ * X + e3) * Y = t * X ^ 3 + W.a₂ * X ^ 2 + e4 * X + e6 := by
  have h := divided_tangent_add_equation W s b3 b4 b6 h3 h4 h6 h₁ h₂ hd
    (tangentLowerSlope_chord W s t w b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂
      hc hd hs h2 h4' h6' h₁)
  rw [← tangentLowerX_scale W s t w a2 u₁ u₂ hs h2,
    ← tangentLowerY_scale W s t w b3 a2 u₁ u₂ v₁ hs h2 h3] at h
  apply (ht.pow 2).left
  rw [Affine.equation_iff, he3, he4, he6] at h
  linear_combination h

end FLT.Mazur.WeierstrassDilatation
