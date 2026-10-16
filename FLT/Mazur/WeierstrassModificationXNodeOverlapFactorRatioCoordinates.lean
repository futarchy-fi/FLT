/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioMap
public import FLT.Mazur.WeierstrassModificationXNodeOverlapOppositeCoordinates

/-!
# Exact corrected coordinates on the actual original node overlap

The two original overlap legs pull the corrected second coordinate back to
the full tangent ratio and its exact inverse, at arbitrary arithmetic order.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "O" => PolynomialNodeOverlap W s
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "H" => polynomialNodeOverlapOppositeEvaluation W s b3 b4 b6 r hr I hI hrI h3
local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "u" => polynomialNodeOverlapRatio W s b3 b4 b6 r hr I hI hrI h3
local notation "U" => G (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "V" => G (polynomialSmallFactor W s b3 b4 b6 r)
local notation "hu" => polynomialNodeOverlap_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3
local notation "hv" => polynomialNodeOverlap_small_isUnit W s b3 b4 b6 r hr I hI hrI h3

/-- The actual full overlap ratio retains precisely the original opposite denominator. -/
theorem polynomialNodeOverlapRatio_denominator : (u : O) * U = V := by
  rw [polynomialNodeOverlapRatio, initialOverlapRatioUnit_coe, mul_assoc,
    (hu).val_inv_mul, mul_one]

/-- The inverse ratio has exactly the original small-factor denominator. -/
theorem polynomialNodeOverlapRatio_inv_denominator : (↑(u)⁻¹ : O) * V = U := by
  rw [← polynomialNodeOverlapRatio_denominator, ← mul_assoc, Units.inv_mul, one_mul]

/-- The original first overlap inclusion has the corrected full ratio coordinate. -/
theorem polynomialFactorRatioMap_overlap_q :
    algebraMap L O (F (NodalFiber.tangentQ τ (-1 : R))) = (u : O) := by
  apply (hu).mul_right_cancel
  rw [polynomialNodeOverlapRatio_denominator]
  have h := congrArg (algebraMap L O)
    (polynomialFactorRatioMap_q_denominator W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)
  rw [map_mul] at h
  exact h

/-- The actual opposite overlap leg gives the inverse parameter, retaining all corrections. -/
theorem polynomialFactorRatioMap_overlap_opposite_q :
    H (F (NodalFiber.tangentQ τ (-1 : R))) = (↑(u)⁻¹ : O) := by
  apply (hv).mul_right_cancel
  rw [polynomialNodeOverlapRatio_inv_denominator]
  have h := congrArg H
    (polynomialFactorRatioMap_q_denominator W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)
  rw [map_mul, polynomialNodeOverlapOppositeEvaluation_reflection,
    polynomialNodeOverlapOppositeEvaluation_reflection,
    initialReflection_opposite, initialReflection_small] at h
  simp only [map_neg] at h
  linear_combination -h

end FLT.Mazur.WeierstrassModificationX
