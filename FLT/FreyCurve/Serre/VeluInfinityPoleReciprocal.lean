/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityKernelOpen

/-!
# Regular reciprocals of the original kernel poles

On the explicit infinity neighborhood, r/(1 - c r) represents 1/(x-c).
It vanishes at infinity and agrees with the original generic pole reciprocal.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (c : K) (hc : c ∈ kernelAbscissae E G)

/-- The inverse of one rescaled kernel factor on the actual neighborhood. -/
def infinityKernelInverse : InfinityKernelRing E G :=
  ↑(infinityKernelFactor_isUnit E G c hc).unit⁻¹

/-- The chosen inverse cancels its original rescaled factor. -/
theorem infinityKernelInverse_mul :
    infinityKernelInverse E G c hc *
      algebraMap (InfinityParameterRing E) (InfinityKernelRing E G)
        (1 - algebraMap K _ c * infinityReciprocal E) = 1 :=
  Units.inv_mul_eq_one.mpr (infinityKernelFactor_isUnit E G c hc).unit_spec

/-- The reciprocal of the original pole x-c, now an actual regular element. -/
def infinityPoleReciprocal : InfinityKernelRing E G :=
  algebraMap _ _ (infinityReciprocal E) * infinityKernelInverse E G c hc

/-- Every pole reciprocal vanishes at the original infinity point. -/
@[simp] theorem infinityPoleReciprocal_value :
    infinityKernelEvaluation E G (infinityPoleReciprocal E G c hc) = 0 := by
  simp [infinityPoleReciprocal]

variable [CharZero K]

omit [DecidableEq K] in
/-- The original generic pole denominator is nonzero. -/
theorem sourceGenericX_sub_ne_zero :
    liftX E RatFunc.X - algebraMap K (FunctionField E) c ≠ 0 := by
  have h := (algebraMap K⟮X⟯ (FunctionField E)).injective.ne (X_sub_C_ne_zero c)
  change algebraMap K⟮X⟯ (FunctionField E) (RatFunc.X - C c) ≠ 0 at h
  rw [map_sub] at h
  exact h

/-- The regular pole reciprocal retains the exact original rational formula. -/
theorem infinityPoleReciprocal_generic :
    infinityKernelHom E G (infinityPoleReciprocal E G c hc) =
      (liftX E RatFunc.X - algebraMap K (FunctionField E) c)⁻¹ := by
  have h := congrArg (infinityKernelHom E G) (infinityKernelInverse_mul E G c hc)
  rw [map_mul, map_one, infinityKernelHom_algebraMap, map_sub, map_one, map_mul,
    AlgHom.commutes, infinityReciprocal_generic] at h
  rw [infinityPoleReciprocal, map_mul, infinityKernelHom_algebraMap,
    infinityReciprocal_generic]
  apply (mul_right_cancel₀ (sourceGenericX_sub_ne_zero E c))
  rw [inv_mul_cancel₀ (sourceGenericX_sub_ne_zero E c)]
  calc
    _ = infinityKernelHom E G (infinityKernelInverse E G c hc) *
        (1 - algebraMap K (FunctionField E) c * (liftX E RatFunc.X)⁻¹) := by
      field_simp [sourceGenericX_ne_zero E]
    _ = 1 := h

end WeierstrassCurve.Velu
