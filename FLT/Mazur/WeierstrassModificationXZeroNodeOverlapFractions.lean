/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroNodeOverlapFactors

/-!
# Reciprocal fractional coordinates on the actual zero-node overlap

The first restriction pulls the fractional coordinate back to the full
tangent ratio. The actual opposite restriction pulls it back to its inverse.
These are identities on the original overlap algebra, not only at points.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local notation "N" => NodalFiber.Coordinate (0 : R)
local notation "L" => PolynomialNodeOpen W 0
local notation "O" => PolynomialNodeOverlap W 0
local notation "V" => polynomialSmallFactor W 0 b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W 0 b3 b4 b6 r
local notation "G" => polynomialNodeOverlapEvaluation W 0 b3 b4 b6 r hr I hI hrI h3
local notation "H" => polynomialNodeOverlapOppositeEvaluation W 0 b3 b4 b6 r hr I hI hrI h3
local notation "v" => polynomialNodeOverlapRatio W 0 b3 b4 b6 r hr I hI hrI h3
local notation "hv" => polynomialNodeOverlap_small_isUnit W 0 b3 b4 b6 r hr I hI hrI h3
local notation "hu" => polynomialNodeOverlap_opposite_isUnit W 0 b3 b4 b6 r hr I hI hrI h3

/-- The complete overlap ratio has its exact denominator equation. -/
theorem polynomialZeroNodeOverlapRatio_mul_opposite : (v : O) * G U = G V := by
  change ↑((hv).unit * (hu).unit⁻¹) * G U = _
  rw [Units.val_mul, mul_assoc, (hu).val_inv_mul, mul_one, IsUnit.unit_spec]

/-- The reciprocal full ratio has its exact small-factor denominator equation. -/
theorem polynomialZeroNodeOverlapRatio_inv_mul_small : (↑((v)⁻¹) : O) * G V = G U := by
  change ↑(((hv).unit * (hu).unit⁻¹)⁻¹) * G V = _
  rw [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, (hv).val_inv_mul,
    mul_one, IsUnit.unit_spec]

include hbot

/-- The original first restriction has precisely the full tangent ratio as fractional coordinate. -/
theorem polynomialZeroNodeOverlap_fraction :
    algebraMap L O (NodalFiber.zeroTangentFraction W.a₁) = (v : O) := by
  have hd : algebraMap L O
      (NodalFiber.zeroTangentQ W.a₁ + algebraMap R L W.a₁) = G U := by
    rw [map_add, ← IsScalarTower.algebraMap_apply R L O,
      polynomialNodeOverlapEvaluation_opposite_of_bot W 0 b3 b4 b6 r hr I hI hrI h3 hbot]
    rw [polynomialNodeOverlapEvaluation_small]
    rfl
  apply (hu).mul_right_cancel
  rw [polynomialZeroNodeOverlapRatio_mul_opposite, ← hd, ← map_mul,
    NodalFiber.zeroTangentFraction_denominator]
  exact (polynomialNodeOverlapEvaluation_small W 0 b3 b4 b6 r hr I hI hrI h3).symm

/-- The actual geometric opposite restriction has the reciprocal fractional coordinate. -/
theorem polynomialZeroNodeOverlap_opposite_fraction :
    H (NodalFiber.zeroTangentFraction W.a₁) = (↑((v)⁻¹) : O) := by
  have hd : H (NodalFiber.zeroTangentQ W.a₁ + algebraMap R L W.a₁) = -G V :=
    polynomialNodeOverlapOppositeEvaluation_denominator_of_bot
      W 0 b3 b4 b6 r hr I hI hrI h3 hbot
  apply (hv).neg.mul_right_cancel
  calc
    H (NodalFiber.zeroTangentFraction W.a₁) * -G V = -G U := by
      rw [← hd, ← map_mul, NodalFiber.zeroTangentFraction_denominator]
      exact polynomialNodeOverlapOppositeEvaluation_q W 0 b3 b4 b6 r hr I hI hrI h3
    _ = (↑((v)⁻¹) : O) * -G V := by
      rw [mul_neg (↑((v)⁻¹) : O) (G V), polynomialZeroNodeOverlapRatio_inv_mul_small]

end FLT.Mazur.WeierstrassModificationX
