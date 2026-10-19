/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityParameterGeneric

/-!
# Removing the finite kernel denominators near infinity

After making 1/x regular, each factor 1 - c/x has value one at infinity.
Their finite product defines a further actual principal neighborhood.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The finite product of the rescaled original kernel denominators. -/
def infinityKernelDenominator : InfinityParameterRing E :=
  ∏ c ∈ kernelAbscissae E G, (1 - algebraMap K _ c * infinityReciprocal E)

/-- The additional denominator has value one at the original infinity point. -/
@[simp] theorem infinityKernelDenominator_value :
    infinityParameterEvaluation E (infinityKernelDenominator E G) = 1 := by
  simp [infinityKernelDenominator]

/-- The additional denominator is nonzero in the actual parameter ring. -/
theorem infinityKernelDenominator_ne_zero : infinityKernelDenominator E G ≠ 0 := by
  intro h
  have := congrArg (infinityParameterEvaluation E) h
  simp at this

/-- An actual affine neighborhood where all original kernel factors are units. -/
abbrev InfinityKernelRing := Localization.Away (infinityKernelDenominator E G)

/-- The original infinity point still lies in this smaller neighborhood. -/
def infinityKernelEvaluation : InfinityKernelRing E G →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (infinityKernelDenominator E G)
    (show IsUnit (infinityParameterEvaluation E (infinityKernelDenominator E G)) by simp)

@[simp] theorem infinityKernelEvaluation_algebraMap (a : InfinityParameterRing E) :
    infinityKernelEvaluation E G (algebraMap _ (InfinityKernelRing E G) a) =
      infinityParameterEvaluation E a :=
  IsLocalization.Away.lift_eq _
    (show IsUnit (infinityParameterEvaluation E (infinityKernelDenominator E G)) by simp) a

/-- Each factor of the original kernel product is now invertible. -/
theorem infinityKernelFactor_isUnit (c : K) (hc : c ∈ kernelAbscissae E G) :
    IsUnit (algebraMap (InfinityParameterRing E) (InfinityKernelRing E G)
      (1 - algebraMap K _ c * infinityReciprocal E)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := InfinityKernelRing E G) (infinityKernelDenominator E G)
  change IsUnit (algebraMap (InfinityParameterRing E) (InfinityKernelRing E G)
    (∏ c ∈ kernelAbscissae E G, (1 - algebraMap K _ c * infinityReciprocal E))) at h
  rw [map_prod] at h
  exact (IsUnit.prod_iff.mp h) c hc

variable [CharZero K]

/-- Generic comparison on this further actual localization. -/
def infinityKernelHom : InfinityKernelRing E G →ₐ[K] FunctionField E :=
  IsLocalization.Away.liftAlgHom (f := infinityParameterHom E) (infinityKernelDenominator E G)
    (isUnit_iff_ne_zero.mpr (by
      change infinityParameterHom E (infinityKernelDenominator E G) ≠ 0
      simpa only [map_zero] using
        (infinityParameterHom_injective E).ne (infinityKernelDenominator_ne_zero E G)))

@[simp] theorem infinityKernelHom_algebraMap (a : InfinityParameterRing E) :
    infinityKernelHom E G (algebraMap _ (InfinityKernelRing E G) a) =
      infinityParameterHom E a :=
  IsLocalization.Away.lift_eq (g := (infinityParameterHom E).toRingHom) _
    (isUnit_iff_ne_zero.mpr (by
      change infinityParameterHom E (infinityKernelDenominator E G) ≠ 0
      simpa only [map_zero] using
        (infinityParameterHom_injective E).ne (infinityKernelDenominator_ne_zero E G))) a

/-- Equality of these regular functions is detected in the original function field. -/
theorem infinityKernelHom_injective : Function.Injective (infinityKernelHom E G) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (infinityKernelDenominator E G)) _).mpr
  intro a b
  change _ ↔ infinityKernelHom E G _ = infinityKernelHom E G _
  constructor
  · exact congrArg (infinityKernelHom E G)
  · intro h
    rw [infinityKernelHom_algebraMap, infinityKernelHom_algebraMap] at h
    exact congrArg (algebraMap _ (InfinityKernelRing E G)) ((infinityParameterHom_injective E) h)

end WeierstrassCurve.Velu
