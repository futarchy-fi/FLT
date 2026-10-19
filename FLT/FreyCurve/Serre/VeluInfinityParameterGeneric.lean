/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityParameter
public import FLT.FreyCurve.Serre.VeluSourceInfinityChart

/-!
# Generic comparison for the regular reciprocal at infinity

The principal neighborhood embeds into the original function field. Its
regular reciprocal is exactly 1/x, with no assumption of local regularity.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- Generic evaluation on the explicit neighborhood D(H). -/
def infinityParameterHom : InfinityParameterRing E →ₐ[K] FunctionField E :=
  IsLocalization.Away.liftAlgHom (f := sourceInfinityChart E) (infinityFactor E)
    (isUnit_iff_ne_zero.mpr (by
      change sourceInfinityChart E (infinityFactor E) ≠ 0
      simpa only [map_zero] using
        (sourceInfinityChart_injective E).ne (infinityFactor_ne_zero E)))

@[simp] theorem infinityParameterHom_algebraMap (a : Coordinate E 1) :
    infinityParameterHom E (algebraMap _ (InfinityParameterRing E) a) =
      sourceInfinityChart E a :=
  IsLocalization.Away.lift_eq (g := (sourceInfinityChart E).toRingHom) _
    (isUnit_iff_ne_zero.mpr (by
      change sourceInfinityChart E (infinityFactor E) ≠ 0
      simpa only [map_zero] using
        (sourceInfinityChart_injective E).ne (infinityFactor_ne_zero E))) a

/-- The actual localized ring injects into the original quadratic model. -/
theorem infinityParameterHom_injective : Function.Injective (infinityParameterHom E) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (infinityFactor E)) _).mpr
  intro a b
  change _ ↔ infinityParameterHom E _ = infinityParameterHom E _
  constructor
  · exact congrArg (infinityParameterHom E)
  · intro h
    rw [infinityParameterHom_algebraMap, infinityParameterHom_algebraMap] at h
    exact congrArg (algebraMap _ (InfinityParameterRing E)) ((sourceInfinityChart_injective E) h)

omit [CharZero K] in
/-- The original generic x-coordinate is nonzero. -/
theorem sourceGenericX_ne_zero : liftX E RatFunc.X ≠ 0 :=
  (algebraMap K⟮X⟯ (FunctionField E)).injective.ne RatFunc.X_ne_zero

/-- The regular reciprocal is the reciprocal original x in the function field. -/
theorem infinityReciprocal_generic :
    infinityParameterHom E (infinityReciprocal E) = (liftX E RatFunc.X)⁻¹ := by
  have h := congrArg (infinityParameterHom E) (infinityReciprocal_relation E)
  rw [map_mul, infinityParameterHom_algebraMap, infinityParameterHom_algebraMap,
    sourceInfinityChart_u, sourceInfinityChart_v] at h
  apply (mul_left_cancel₀ (div_ne_zero (sourceGenericX_ne_zero E) (sourceGenericY_ne_zero E)))
  rw [h]
  field_simp [sourceGenericX_ne_zero E, sourceGenericY_ne_zero E]

end WeierstrassCurve.Velu
