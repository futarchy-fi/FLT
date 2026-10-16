/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroNodeOverlapFractions

/-!
# The original ordered infinity tangent is the reciprocal fractional parameter

On the actual zero-node intersection the original y is a unit. Its original
X/Y coordinate satisfies 1+a₁ X/Y = (small/opposite)⁻¹. This fixes the
orientation needed to compare with the existing full Laurent infinity chart.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)
local notation "O" => PolynomialNodeOverlap W 0
local notation "V" => polynomialSmallFactor W 0 b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W 0 b3 b4 b6 r
local notation "G" => polynomialNodeOverlapEvaluation W 0 b3 b4 b6 r hr I hI hrI h3
local notation "hv" => polynomialNodeOverlap_small_isUnit W 0 b3 b4 b6 r hr I hI hrI h3
local notation "hu" => polynomialNodeOverlap_opposite_isUnit W 0 b3 b4 b6 r hr I hI hrI h3
local notation "v" => polynomialNodeOverlapRatio W 0 b3 b4 b6 r hr I hI hrI h3

include hbot

/-- The original slope equals the full small factor when the arithmetic ideal vanishes. -/
theorem polynomialZeroNodeOverlap_slope : G (WeierstrassModificationX.v W 0 b3 b4 b6) = G V := by
  have hr0 : r = 0 := by simpa only [hbot, Ideal.map_bot, Ideal.mem_bot] using hrI
  simp only [polynomialSmallFactor, hr0, map_zero, sub_zero]

/-- The original X and Y retain their exact quotient relation on the original overlap. -/
theorem polynomialZeroNodeOverlap_y :
    G (y W 0 b3 b4 b6) = G (x W 0 b3 b4 b6) * G V := by
  rw [y, map_mul, polynomialZeroNodeOverlap_slope W b3 b4 b6 r hr I hI hrI h3 hbot]

/-- The full original Y function is invertible on this original zero-fiber intersection. -/
theorem polynomialZeroNodeOverlap_y_isUnit : IsUnit (G (y W 0 b3 b4 b6)) := by
  rw [polynomialZeroNodeOverlap_y W b3 b4 b6 r hr I hI hrI h3 hbot,
    polynomialFactors_horizontal W 0 b3 b4 b6 r hr, map_mul]
  exact ((hv).mul hu).mul hv

/-- The original homogeneous X/Y function on the full infinity boundary. -/
def polynomialZeroNodeOverlapXOverY : O :=
  G (x W 0 b3 b4 b6) *
    ↑((polynomialZeroNodeOverlap_y_isUnit W b3 b4 b6 r hr I hI hrI h3 hbot).unit⁻¹)

/-- The original X/Y is exactly the reciprocal original slope on the entire overlap. -/
theorem polynomialZeroNodeOverlapXOverY_mul_small :
    polynomialZeroNodeOverlapXOverY W b3 b4 b6 r hr I hI hrI h3 hbot * G V = 1 := by
  have hy := polynomialZeroNodeOverlap_y_isUnit W b3 b4 b6 r hr I hI hrI h3 hbot
  rw [polynomialZeroNodeOverlapXOverY, mul_right_comm,
    ← polynomialZeroNodeOverlap_y W b3 b4 b6 r hr I hI hrI h3 hbot]
  exact hy.mul_val_inv

/-- The existing ordered infinity Laurent parameter has the reciprocal fractional orientation. -/
theorem polynomialZeroNodeOverlap_infinity_tangent :
    1 + algebraMap R O W.a₁ *
      polynomialZeroNodeOverlapXOverY W b3 b4 b6 r hr I hI hrI h3 hbot = (↑((v)⁻¹) : O) := by
  apply (hv).mul_right_cancel
  rw [add_mul, one_mul, mul_assoc,
    polynomialZeroNodeOverlapXOverY_mul_small, mul_one,
    polynomialZeroNodeOverlapRatio_inv_mul_small,
    polynomialNodeOverlapEvaluation_opposite_of_bot W 0 b3 b4 b6 r hr I hI hrI h3 hbot]

end FLT.Mazur.WeierstrassModificationX
