/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceFractionField
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Principal localizations inside the original cubic function field

Localizing the actual source affine chart at a nonzero function embeds it in
the original quadratic field. This detects equations on explicit principal opens.
-/

@[expose] public noncomputable section

open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)
  (d : Coordinate E 2) (hd : d ≠ 0)

/-- The actual principal localization maps into the original function field. -/
def sourceLocalizationHom : Localization.Away d →ₐ[K] FunctionField E :=
  IsLocalization.Away.liftAlgHom d
    (isUnit_iff_ne_zero.mpr ((sourceGenericChart_injective E).ne hd))

/-- The localized map retains the original value of every affine function. -/
@[simp] theorem sourceLocalizationHom_algebraMap (a : Coordinate E 2) :
    sourceLocalizationHom E d hd (algebraMap _ (Localization.Away d) a) =
      sourceGenericChart E a :=
  IsLocalization.Away.lift_eq d
    (isUnit_iff_ne_zero.mpr ((sourceGenericChart_injective E).ne hd)) a

/-- Equality in this principal localization is detected in the original field. -/
theorem sourceLocalizationHom_injective : Function.Injective (sourceLocalizationHom E d hd) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d) _).mpr
  intro a b
  change _ ↔ sourceLocalizationHom E d hd _ = sourceLocalizationHom E d hd _
  constructor
  · intro h
    exact congrArg (sourceLocalizationHom E d hd) h
  · intro h
    rw [sourceLocalizationHom_algebraMap, sourceLocalizationHom_algebraMap] at h
    exact congrArg (algebraMap _ (Localization.Away d)) ((sourceGenericChart_injective E) h)

/-- The distinguished inverse maps to the inverse of the original affine function. -/
theorem sourceLocalizationHom_invSelf :
    sourceLocalizationHom E d hd (IsLocalization.Away.invSelf d) =
      (sourceGenericChart E d)⁻¹ := by
  apply (mul_left_cancel₀ ((sourceGenericChart_injective E).ne hd))
  rw [mul_inv_cancel₀ ((sourceGenericChart_injective E).ne hd)]
  simpa only [map_mul, map_one, sourceLocalizationHom_algebraMap] using
    congrArg (sourceLocalizationHom E d hd)
      (IsLocalization.Away.mul_invSelf (S := Localization.Away d) d)

end WeierstrassCurve.Velu
