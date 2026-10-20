/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchFormula

/-!
# Strict-branch formulas with a smaller output scale

Factor the input scale as t * w. The branch equation then divides its
ordinate and tangent slope by t, even when the constant is not divisible
by the whole input scale. The output coordinates contract to the original sum.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s t w b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
local notation "C" => v₁ + W.a₁ * u₁ + b3
local notation "D" => v₁ + v₂ + W.a₁ * u₂ + b3

/-- The branch inverse constructs the ordinate divided by the smaller scale. -/
def tangentLowerOrdinate (hc : IsUnit C) : R :=
  (w * u₁ ^ 3 + a2 * u₁ ^ 2 + b4' * u₁ + b6') * ↑hc.unit⁻¹

/-- The input equation proves divisibility by the smaller scale. -/
theorem tangentLowerOrdinate_mul (hc : IsUnit C)
    (hs : s = t * w) (h2 : W.a₂ = t * a2)
    (h4 : b4 = t * b4') (h6 : b6 = t * b6')
    (he : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6) :
    t * tangentLowerOrdinate W w b3 a2 b4' b6' u₁ v₁ hc = v₁ := by
  apply hc.mul_left_inj.mp
  unfold tangentLowerOrdinate
  rw [mul_assoc t, mul_assoc, hc.val_inv_mul, mul_one]
  rw [hs, h2, h4, h6] at he
  linear_combination -he

/-- The original tangent slope divided by the smaller output scale. -/
def tangentLowerSlope (hc : IsUnit C) (hd : IsUnit D) : R :=
  (w * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + a2 * (u₁ + u₂) + b4' -
    W.a₁ * tangentLowerOrdinate W w b3 a2 b4' b6' u₁ v₁ hc) * ↑hd.unit⁻¹

/-- The constructed slope satisfies the entire original chord equation. -/
theorem tangentLowerSlope_chord (hc : IsUnit C) (hd : IsUnit D)
    (hs : s = t * w) (h2 : W.a₂ = t * a2)
    (h4 : b4 = t * b4') (h6 : b6 = t * b6')
    (he : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6) :
    (t * tangentLowerSlope W w b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd) * D =
      s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁ := by
  have hv := tangentLowerOrdinate_mul W s t w b3 b4 b6 a2 b4' b6' u₁ v₁
    hc hs h2 h4 h6 he
  unfold tangentLowerSlope
  rw [mul_assoc t, mul_assoc, hd.val_inv_mul, mul_one, hs, h2, h4]
  linear_combination -W.a₁ * hv

/-- The lower-depth abscissa of the sum. -/
def tangentLowerX (l : R) : R := t * l ^ 2 + W.a₁ * l - a2 - w * (u₁ + u₂)

/-- The lower-depth ordinate of the sum. -/
def tangentLowerY (l : R) : R :=
  -(t * l + W.a₁) * tangentLowerX W t w a2 u₁ u₂ l +
    s * l * u₁ - w * v₁ - w * b3

/-- Multiplication by the output scale recovers the original sum abscissa. -/
theorem tangentLowerX_scale (hs : s = t * w) (h2 : W.a₂ = t * a2) (l : R) :
    t * tangentLowerX W t w a2 u₁ u₂ l =
      W.toAffine.addX (s * u₁) (s * u₂) (t * l) := by
  simp only [tangentLowerX, Affine.addX, hs, h2]
  ring

/-- Multiplication by the output scale recovers the original sum ordinate. -/
theorem tangentLowerY_scale (hs : s = t * w) (h2 : W.a₂ = t * a2)
    (h3 : W.a₃ = s * b3) (l : R) :
    t * tangentLowerY W s t w b3 a2 u₁ u₂ v₁ l =
      W.toAffine.addY (s * u₁) (s * u₂) (s * v₁) (t * l) := by
  simp only [tangentLowerY, tangentLowerX, Affine.addY, Affine.negY,
    Affine.negAddY, Affine.addX, h2, h3, hs]
  ring

end FLT.Mazur.WeierstrassDilatation
