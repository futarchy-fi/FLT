/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityTargetOpen

/-!
# Original generic coordinates on the final infinity neighborhood

The normalized regular functions retain exactly imageX/imageY and 1/imageY
in the original quadratic field, preparing comparison of actual scheme maps.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- Generic evaluation on the final actual infinity neighborhood. -/
def infinityTargetHom : InfinityTargetRing E G →ₐ[K] FunctionField E :=
  IsLocalization.Away.liftAlgHom (f := infinityKernelHom E G) (infinityScaledY E G)
    (isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using
        (infinityKernelHom_injective E G).ne (infinityScaledY_ne_zero E G)))

@[simp] theorem infinityTargetHom_algebraMap (a : InfinityKernelRing E G) :
    infinityTargetHom E G (algebraMap _ (InfinityTargetRing E G) a) =
      infinityKernelHom E G a :=
  IsLocalization.Away.lift_eq (g := (infinityKernelHom E G).toRingHom) _
    (isUnit_iff_ne_zero.mpr (by
      change infinityKernelHom E G (infinityScaledY E G) ≠ 0
      simpa only [map_zero] using
        (infinityKernelHom_injective E G).ne (infinityScaledY_ne_zero E G))) a

/-- Generic comparison of the last normalizing inverse. -/
theorem infinityTargetHom_inverse :
    infinityTargetHom E G (IsLocalization.Away.invSelf (infinityScaledY E G)) =
      liftY E E RatFunc.X 1 /
        liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  have h := congrArg (infinityTargetHom E G)
    (IsLocalization.Away.mul_invSelf (S := InfinityTargetRing E G) (infinityScaledY E G))
  rw [map_mul, map_one, infinityTargetHom_algebraMap, infinityScaledY_generic] at h
  apply (mul_left_cancel₀ (div_ne_zero (infinityImageY_ne_zero E G) (sourceGenericY_ne_zero E)))
  rw [h]
  field_simp [infinityImageY_ne_zero E G, sourceGenericY_ne_zero E]

/-- The regular target x/y coordinate has the original generic ratio. -/
theorem infinityTargetCoordinates_x_generic :
    infinityTargetHom E G (infinityTargetCoordinates E G 0) =
      liftX E (xFunction E G) /
        liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  change infinityTargetHom E G (_ * algebraMap (InfinityKernelRing E G) _
    (infinityScaledX E G)) = _
  rw [map_mul, infinityTargetHom_inverse, infinityTargetHom_algebraMap,
    infinityScaledX_generic]
  field_simp [sourceGenericY_ne_zero E]

/-- The regular target z/y coordinate has the original generic reciprocal. -/
theorem infinityTargetCoordinates_z_generic :
    infinityTargetHom E G (infinityTargetCoordinates E G 2) =
      (liftY E (curve E G) (xFunction E G) (slopeFunction E G))⁻¹ := by
  change infinityTargetHom E G (_ * algebraMap (InfinityKernelRing E G) _
    (infinityV E G)) = _
  rw [map_mul, infinityTargetHom_inverse, infinityTargetHom_algebraMap, infinityV_generic]
  field_simp [sourceGenericY_ne_zero E]

attribute [local irreducible] infinityTargetCoordinates infinityTargetHom

/-- The final homogeneous coordinates retain the original generic rational map. -/
theorem infinityTargetCoordinates_generic (i : Fin 3) :
    infinityTargetHom E G (infinityTargetCoordinates E G i) =
      ![liftX E (xFunction E G) /
          liftY E (curve E G) (xFunction E G) (slopeFunction E G),
        1, (liftY E (curve E G) (xFunction E G) (slopeFunction E G))⁻¹] i := by
  fin_cases i
  · exact infinityTargetCoordinates_x_generic E G
  · exact (congrArg (infinityTargetHom E G) (infinityTargetCoordinates_y E G)).trans
      (map_one (infinityTargetHom E G))
  · exact infinityTargetCoordinates_z_generic E G

end WeierstrassCurve.Velu
