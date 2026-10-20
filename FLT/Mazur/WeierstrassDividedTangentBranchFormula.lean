/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentFormula
public import FLT.Mazur.WeierstrassDilatationMorphism

/-!
# Divide the tangent output on a strict branch

A unit complementary branch factor constructs the divided ordinate. The
second slope denominator then constructs a slope divisible by the scale.
Explicit output coordinates lift the sum into the divided chart, even when
its original output is the singular point.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (s b3 b4 b6 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
local notation "D" => v₁ + v₂ + W.a₁ * u₂ + b3
local notation "C" => v₁ + W.a₁ * u₁ + b3

/-- Divide the first ordinate using its complementary branch factor. -/
def tangentBranchOrdinate (hc : IsUnit C) : R :=
  (u₁ ^ 3 + a2 * u₁ ^ 2 + b4' * u₁ + b6') * ↑hc.unit⁻¹

/-- The branch equation proves ordinate divisibility; it is not supplied as data. -/
theorem tangentBranchOrdinate_mul (hc : IsUnit C)
    (h2 : W.a₂ = s * a2) (h4 : b4 = s * b4') (h6 : b6 = s * b6')
    (he : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6) :
    s * tangentBranchOrdinate W b3 a2 b4' b6' u₁ v₁ hc = v₁ := by
  apply hc.mul_left_inj.mp
  have hinv : (↑hc.unit⁻¹ : R) * C = 1 := hc.val_inv_mul
  unfold tangentBranchOrdinate
  calc
    s * ((u₁ ^ 3 + a2 * u₁ ^ 2 + b4' * u₁ + b6') * ↑hc.unit⁻¹) * C =
        s * (u₁ ^ 3 + a2 * u₁ ^ 2 + b4' * u₁ + b6') := by
          rw [mul_assoc s, mul_assoc, hinv, mul_one]
    _ = v₁ * C := by rw [h2, h4, h6] at he; linear_combination -he

/-- Construct the divided tangent slope on the two actual principal opens. -/
def tangentBranchSlope (hc : IsUnit C) (hd : IsUnit D) : R :=
  (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2 + a2 * (u₁ + u₂) + b4' -
    W.a₁ * tangentBranchOrdinate W b3 a2 b4' b6' u₁ v₁ hc) * ↑hd.unit⁻¹

/-- The constructed divided slope scales to the genuine tangent slope. -/
theorem tangentBranchSlope_mul (hc : IsUnit C) (hd : IsUnit D)
    (h2 : W.a₂ = s * a2) (h4 : b4 = s * b4') (h6 : b6 = s * b6')
    (he : v₁ ^ 2 + (W.a₁ * u₁ + b3) * v₁ =
      s * u₁ ^ 3 + W.a₂ * u₁ ^ 2 + b4 * u₁ + b6)
    (l : R) (hl : l * D =
      s * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2) + W.a₂ * (u₁ + u₂) + b4 - W.a₁ * v₁) :
    s * tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd = l := by
  apply hd.mul_left_inj.mp
  have hinv : (↑hd.unit⁻¹ : R) * D = 1 := hd.val_inv_mul
  have hv := tangentBranchOrdinate_mul W s b3 b4 b6 a2 b4' b6' u₁ v₁ hc h2 h4 h6 he
  unfold tangentBranchSlope
  rw [mul_assoc s, mul_assoc, hinv, mul_one, hl, h2, h4]
  linear_combination -W.a₁ * hv

/-- The divided abscissa of a tangent output whose slope is divisible by the scale. -/
def tangentBranchX (k : R) : R := s * k ^ 2 + W.a₁ * k - a2 - u₁ - u₂

/-- The divided ordinate retains the original unsheared addition formula. -/
def tangentBranchY (k : R) : R :=
  -(s * k + W.a₁) * tangentBranchX W s a2 u₁ u₂ k + s * k * u₁ - v₁ - b3

/-- The constructed divided abscissa has exactly the original addition coordinate. -/
theorem tangentBranchX_scale (h2 : W.a₂ = s * a2) (k : R) :
    s * tangentBranchX W s a2 u₁ u₂ k =
      W.toAffine.addX (s * u₁) (s * u₂) (s * k) := by
  simp only [tangentBranchX, Affine.addX, h2]
  ring

/-- The constructed divided ordinate has exactly the original addition coordinate. -/
theorem tangentBranchY_scale (h2 : W.a₂ = s * a2) (h3 : W.a₃ = s * b3) (k : R) :
    s * tangentBranchY W s b3 a2 u₁ u₂ v₁ k =
      W.toAffine.addY (s * u₁) (s * u₂) (s * v₁) (s * k) := by
  simp only [tangentBranchY, tangentBranchX, Affine.addY, Affine.negY,
    Affine.negAddY, Affine.addX, h2, h3]
  ring

end FLT.Mazur.WeierstrassDilatation
