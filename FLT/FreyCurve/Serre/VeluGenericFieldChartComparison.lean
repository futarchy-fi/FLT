/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGenericFunctionFieldHom
public import FLT.FreyCurve.Serre.VeluSourceChart

/-!
# The full quadratic field map retains the original affine Vélu formulas

The target's original x and y coordinates map to the actual generic Vélu
coordinates. Thus the full field map and the existing generic chart agree.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

omit [DecidableEq K] in
/-- The original uncompleted y coordinate expressed through the quadratic generator. -/
theorem sourceGenericY_completed :
    liftY E E RatFunc.X 1 =
      (QuadraticAlgebra.omega - algebraMap K _ E.a₁ * liftX E RatFunc.X -
        algebraMap K _ E.a₃) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : FunctionField E) ≠ 0)).mpr
  apply QuadraticAlgebra.ext
  all_goals simp [liftX, liftY]

/-- The full original field map sends y to the original generic Vélu y function. -/
theorem veluGenericFunctionFieldHom_sourceY :
    veluGenericFunctionFieldHom E G hodd (liftY (curve E G) (curve E G) RatFunc.X 1) =
      liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  rw [sourceGenericY_completed]
  simp only [map_div₀, map_sub, map_mul, map_ofNat, AlgHom.commutes,
    veluGenericFunctionFieldHom_omega, veluGenericFunctionFieldHom_liftX,
    veluGenericXFieldHom_X]
  apply (div_eq_iff (by norm_num : (2 : FunctionField E) ≠ 0)).mpr
  apply QuadraticAlgebra.ext
  all_goals simp [veluGenericCompletedY, liftX, liftY]

/-- The full field homomorphism agrees with evaluation of every target affine function. -/
theorem veluGenericFunctionFieldHom_chart :
    (veluGenericFunctionFieldHom E G hodd).comp (sourceGenericChart (curve E G)) =
      veluGenericChart E G hodd := by
  apply hom_ext
  intro i
  fin_cases i
  · change veluGenericFunctionFieldHom E G hodd
      (sourceGenericChart (curve E G) (coord (curve E G) 2 0)) =
        veluGenericChart E G hodd (coord (curve E G) 2 0)
    rw [sourceGenericChart_x, veluGenericFunctionFieldHom_liftX,
      veluGenericXFieldHom_X, veluGenericChart_x]
  · change veluGenericFunctionFieldHom E G hodd
      (sourceGenericChart (curve E G) (coord (curve E G) 2 1)) =
        veluGenericChart E G hodd (coord (curve E G) 2 1)
    rw [sourceGenericChart_y, veluGenericFunctionFieldHom_sourceY,
      veluGenericChart_y]
  · change ((veluGenericFunctionFieldHom E G hodd).comp (sourceGenericChart (curve E G)))
      (coord (curve E G) 2 2) = veluGenericChart E G hodd (coord (curve E G) 2 2)
    rw [coord_self, map_one, map_one]

end WeierstrassCurve.Velu
