/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityScaledGeneric

/-!
# The scaled target y-coordinate is regular and nonzero at infinity

Recover the original y-image divided by source y from the completed-y formula.
Its value is one, so it defines the final principal neighborhood for chart Y = 1.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The original y-image scaled by source y, as an actual regular function. -/
def infinityScaledY : InfinityKernelRing E G :=
  (infinitySlope E G * (2 + algebraMap K _ E.a₁ * infinityU E G +
      algebraMap K _ E.a₃ * infinityV E G) -
    algebraMap K _ (curve E G).a₁ * infinityScaledX E G -
    algebraMap K _ (curve E G).a₃ * infinityV E G) * algebraMap K _ (2⁻¹ : K)

/-- The scaled ordinate is a unit at the original infinity point. -/
@[simp] theorem infinityScaledY_value :
    infinityKernelEvaluation E G (infinityScaledY E G) = 1 := by
  simp [infinityScaledY, map_ofNat]

omit [DecidableEq K] in
/-- The uncompleted generic ordinate is recovered from the original completed formula. -/
theorem infinity_liftY_recovery (E' : WeierstrassCurve K) (f g : K⟮X⟯) :
    liftX E g * (2 * liftY E E RatFunc.X 1 +
        algebraMap K _ E.a₁ * liftX E RatFunc.X + algebraMap K _ E.a₃) -
      algebraMap K _ E'.a₁ * liftX E f - algebraMap K _ E'.a₃ =
        2 * liftY E E' f g := by
  apply QuadraticAlgebra.ext
  all_goals simp [liftX, liftY]; ring

/-- The regular ordinate is exactly the original image divided by source y. -/
theorem infinityScaledY_generic :
    infinityKernelHom E G (infinityScaledY E G) =
      liftY E (curve E G) (xFunction E G) (slopeFunction E G) / liftY E E RatFunc.X 1 := by
  simp only [infinityScaledY, map_mul, map_sub, map_add, map_ofNat, AlgHom.commutes,
    infinitySlope_generic, infinityU_generic, infinityV_generic, infinityScaledX_generic]
  rw [map_inv₀, map_ofNat]
  apply (mul_right_cancel₀ (sourceGenericY_ne_zero E))
  rw [div_mul_cancel₀ _ (sourceGenericY_ne_zero E)]
  calc
    _ = (liftX E (slopeFunction E G) * (2 * liftY E E RatFunc.X 1 +
        algebraMap K _ E.a₁ * liftX E RatFunc.X + algebraMap K _ E.a₃) -
      algebraMap K _ (curve E G).a₁ * liftX E (xFunction E G) -
      algebraMap K _ (curve E G).a₃) / 2 := by
        field_simp [sourceGenericY_ne_zero E]
    _ = _ := by rw [infinity_liftY_recovery]; ring

/-- The final denominator is nonzero in the actual neighborhood ring. -/
theorem infinityScaledY_ne_zero : infinityScaledY E G ≠ 0 := by
  intro h
  have := congrArg (infinityKernelEvaluation E G) h
  simp at this

end WeierstrassCurve.Velu
