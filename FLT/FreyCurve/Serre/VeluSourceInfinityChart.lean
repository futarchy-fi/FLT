/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceLocalization
public import FLT.Mazur.WeierstrassProductOverlapFlat

/-!
# The original infinity chart inside the function field

Pass through the actual affine/infinity overlap. Both its localization map
and its chart transition are injective, so the infinity chart embeds faithfully.
-/

@[expose] public noncomputable section

open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K)

/-- The original generic y-coordinate is nonzero, detected by its quadratic part. -/
theorem sourceGenericY_ne_zero : liftY E E RatFunc.X 1 ≠ 0 := by
  intro h
  have hi := congrArg QuadraticAlgebra.im h
  norm_num [liftY] at hi

/-- The original affine y-coordinate is a nonzero function. -/
theorem sourceCoordY_ne_zero : coord E 2 1 ≠ 0 := by
  intro h
  apply sourceGenericY_ne_zero E
  simpa only [sourceGenericChart_y, map_zero] using congrArg (sourceGenericChart E) h

/-- Evaluation on the actual overlap with the infinity chart. -/
def sourceInfinityOverlapHom : Overlap E 2 1 →ₐ[K] FunctionField E :=
  sourceLocalizationHom E (coord E 2 1) (sourceCoordY_ne_zero E)

/-- The homogeneous normalizing inverse is exactly the reciprocal original y. -/
theorem sourceInfinityOverlapHom_inverse :
    sourceInfinityOverlapHom E (overlapInverse E 2 1) =
      (liftY E E RatFunc.X 1)⁻¹ := by
  have h := congrArg (sourceInfinityOverlapHom E) (overlapInverse_mul E 2 1)
  change _ = _ at h
  rw [map_mul, map_one] at h
  change _ * sourceLocalizationHom E _ _ (algebraMap _ _ (coord E 2 1)) = 1 at h
  rw [sourceLocalizationHom_algebraMap, sourceGenericChart_y] at h
  apply (mul_right_cancel₀ (sourceGenericY_ne_zero E))
  rw [h, inv_mul_cancel₀ (sourceGenericY_ne_zero E)]

/-- The infinity chart evaluated in the original quadratic function field. -/
def sourceInfinityChart : Coordinate E 1 →ₐ[K] FunctionField E :=
  (sourceInfinityOverlapHom E).comp (transitionBase E 2 1)

/-- Evaluation of any normalized infinity-chart coordinate. -/
theorem sourceInfinityChart_coord (i : Fin 3) :
    sourceInfinityChart E (coord E 1 i) =
      (liftY E E RatFunc.X 1)⁻¹ * sourceGenericChart E (coord E 2 i) := by
  rw [sourceInfinityChart, AlgHom.comp_apply, transitionBase_coord, map_mul,
    sourceInfinityOverlapHom_inverse]
  rw [sourceInfinityOverlapHom, overlapCoord, sourceLocalizationHom_algebraMap]

@[simp] theorem sourceInfinityChart_u :
    sourceInfinityChart E (coord E 1 0) =
      liftX E RatFunc.X / liftY E E RatFunc.X 1 := by
  rw [sourceInfinityChart_coord, sourceGenericChart_x, div_eq_mul_inv, mul_comm]

@[simp] theorem sourceInfinityChart_v :
    sourceInfinityChart E (coord E 1 2) = (liftY E E RatFunc.X 1)⁻¹ := by
  rw [sourceInfinityChart_coord, coord_self, map_one, mul_one]

/-- Passing through the overlap loses no functions of the infinity chart. -/
theorem sourceInfinityChart_injective : Function.Injective (sourceInfinityChart E) := by
  have ht : Function.Injective (transitionBase E 2 1) := by
    have h : (transitionBase E 2 1) =
        (overlapEquiv E 2 1).toAlgHom.comp (overlapRestriction E 1 2) := by
      apply hom_ext
      intro i
      change _ = transition E 2 1 (overlapCoord E 1 2 i)
      rw [transition_coord, transitionBase_coord]
    rw [h]
    exact (overlapEquiv E 2 1).injective.comp (infinityOverlapRestriction_injective E)
  exact (sourceLocalizationHom_injective E (coord E 2 1)
    (sourceCoordY_ne_zero E)).comp ht

end WeierstrassCurve.Velu
