/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineNonkernelOpen

/-!
# The regular Vélu morphism retains the original point coordinates

Evaluate the actual localized functions at original affine points outside
the kernel. Their values are the original xMap and yMap coordinate sums.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  {x y : K} (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G)

/-- The distinguished inverse specializes to the actual inverse denominator. -/
theorem veluAffinePointLift_invSelf :
    veluAffinePointLift E G hP hPG (IsLocalization.Away.invSelf (veluAffineDenominator E G)) =
      (veluSourcePointChart E hP (veluAffineDenominator E G))⁻¹ := by
  apply mul_left_cancel₀ (veluSourcePointChart_denominator E G hP hPG)
  rw [mul_inv_cancel₀ (veluSourcePointChart_denominator E G hP hPG)]
  simpa only [map_mul, map_one, veluAffinePointLift_algebraMap] using
    congrArg (veluAffinePointLift E G hP hPG)
      (IsLocalization.Away.mul_invSelf (S := VeluAffineLocalization E G)
        (veluAffineDenominator E G))

/-- The actual localized fraction specializes by ordinary polynomial evaluation. -/
theorem veluAffinePointLift_fraction (p : K[X]) :
    veluAffinePointLift E G hP hPG (veluAffineFraction E G p) =
      p.eval x / ((xFunction E G).denom * (slopeFunction E G).denom).eval x := by
  rw [veluAffineFraction, map_mul, veluAffinePointLift_algebraMap,
    veluAffinePointLift_invSelf, veluAffineDenominator,
    veluSourcePointChart_polynomial, veluSourcePointChart_polynomial]
  rw [div_eq_mul_inv]

/-- The regular x-function specializes to evaluation of the original rational x-function. -/
theorem veluAffinePointLift_x_eval :
    veluAffinePointLift E G hP hPG (veluAffineX E G) =
      RatFunc.eval (RingHom.id K) x (xFunction E G) := by
  have hx := x_not_mem_kernelAbscissae E G hP hPG
  rw [veluAffineX, veluAffinePointLift_fraction, Polynomial.eval_mul, Polynomial.eval_mul,
    mul_div_mul_right _ _ (regular_eval_slopeFunction E G x hx).1]
  simp only [RatFunc.eval, Polynomial.eval₂_id]

/-- The regular slope specializes to evaluation of the original rational slope. -/
theorem veluAffinePointLift_slope_eval :
    veluAffinePointLift E G hP hPG (veluAffineSlope E G) =
      RatFunc.eval (RingHom.id K) x (slopeFunction E G) := by
  have hx := x_not_mem_kernelAbscissae E G hP hPG
  rw [veluAffineSlope, veluAffinePointLift_fraction, Polynomial.eval_mul, Polynomial.eval_mul,
    mul_comm ((xFunction E G).denom.eval x),
    mul_div_mul_right _ _ (regular_eval_xFunction E G x hx).1]
  simp only [RatFunc.eval, Polynomial.eval₂_id]

variable [CharZero K] (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
include hodd

/-- The regular x-function has exactly the original Vélu coordinate-sum value. -/
theorem veluAffinePointLift_x :
    veluAffinePointLift E G hP hPG (veluAffineX E G) = xMap E G (.some x y hP) := by
  rw [veluAffinePointLift_x_eval,
    (regular_eval_xFunction E G x (x_not_mem_kernelAbscissae E G hP hPG)).2,
    xMap_eq_sum_abscissae E G hodd hP hPG]

/-- The regular slope has exactly the original Vélu slope-factor value. -/
theorem veluAffinePointLift_slope :
    veluAffinePointLift E G hP hPG (veluAffineSlope E G) = slopeFactor E G x := by
  rw [veluAffinePointLift_slope_eval,
    (regular_eval_slopeFunction E G x (x_not_mem_kernelAbscissae E G hP hPG)).2,
    slopeFactor_eq_sum_abscissae E G hodd x]

/-- The regular y-function has exactly the original uncompleted Vélu coordinate-sum value. -/
theorem veluAffinePointLift_y :
    veluAffinePointLift E G hP hPG (veluAffineY E G) = yMap E G (.some x y hP) := by
  simp only [veluAffineY, map_mul, map_sub, map_add, map_ofNat, AlgHom.commutes,
    veluAffinePointLift_algebraMap, veluAffinePointLift_x E G hP hPG hodd,
    veluAffinePointLift_slope E G hP hPG hodd, veluSourcePointChart, evaluation_coord,
    Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.algebraMap_self, RingHom.id_apply]
  change (slopeFactor E G x * (2 * y + E.a₁ * x + E.a₃) -
    E.a₁ * xMap E G (.some x y hP) - E.a₃) * 2⁻¹ = _
  have hc := completed_yMap E G hP hPG
  linear_combination -hc / 2

end WeierstrassCurve.Velu
