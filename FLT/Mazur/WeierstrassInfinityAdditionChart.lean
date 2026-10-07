/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionSlope

/-!
# A regular addition morphism on the infinity product neighborhood

The integral formula using dz/dx satisfies the cubic in the actual localized
product ring. Inverting its output Y coordinate gives an algebra map from
the Y = 1 curve chart. The following module identifies the infinity section
inside this neighborhood.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Homogeneous output coordinates on the dz/dx domain of the Y-chart product. -/
def infinityOutputCoordinates : Fin 3 → InfinitySlopeOpen W :=
  infinityAdditionXYZ (W.map (algebraMap R (InfinitySlopeOpen W)))
    (infinityLeft W (infinitySlopeRestriction W) 0)
    (infinityRight W (infinitySlopeRestriction W) 0)
    (infinityLeft W (infinitySlopeRestriction W) 2) (infinitySlope W)

/-- The actual universal output satisfies the cubic, including on the diagonal. -/
theorem infinityOutputCoordinates_equation :
    (W.map (algebraMap R (InfinitySlopeOpen W))).toProjective.Equation
      (infinityOutputCoordinates W) :=
  infinityAdditionXYZ_equation _ (infinityLeft_equation W _)
    (infinitySlope_mul_difference W) (infinitySlope_mul_den W)

/-- The open where the infinity addition output can be normalized in the Y chart. -/
abbrev InfinityAdditionOpen := Localization.Away (infinityOutputCoordinates W 1)

/-- Restriction from the slope domain to the normalized output domain. -/
def infinityOutputRestriction : InfinitySlopeOpen W →ₐ[R] InfinityAdditionOpen W :=
  IsScalarTower.toAlgHom R (InfinitySlopeOpen W) (InfinityAdditionOpen W)

/-- The full domain map to the original product of Y charts. -/
def infinityAdditionRestriction : ChartProduct W 1 1 →ₐ[R] InfinityAdditionOpen W :=
  (infinityOutputRestriction W).comp (infinitySlopeRestriction W)

/-- The normalizing output coordinate is a unit. -/
theorem infinityOutputY_isUnit :
    IsUnit (infinityOutputRestriction W (infinityOutputCoordinates W 1)) :=
  IsLocalization.Away.algebraMap_isUnit (infinityOutputCoordinates W 1)

/-- Inverse of the homogeneous output Y coordinate. -/
def infinityOutputInverse : InfinityAdditionOpen W :=
  ↑(infinityOutputY_isUnit W).unit⁻¹

/-- The output inverse cancels the Y coordinate. -/
@[simp] theorem infinityOutputInverse_mul :
    infinityOutputInverse W * infinityOutputRestriction W (infinityOutputCoordinates W 1) = 1 :=
  Units.inv_mul_eq_one.mpr (infinityOutputY_isUnit W).unit_spec

/-- Restriction preserves the homogeneous cubic equation. -/
theorem infinityRestrictedOutput_equation :
    (W.map (algebraMap R (InfinityAdditionOpen W))).toProjective.Equation
      (infinityOutputRestriction W ∘ infinityOutputCoordinates W) := by
  have h := (infinityOutputCoordinates_equation W).map
    (infinityOutputRestriction W).toRingHom
  change ((W.map (algebraMap R (InfinitySlopeOpen W))).map
    (infinityOutputRestriction W).toRingHom).toProjective.Equation _ at h
  have he : (W.map (algebraMap R (InfinitySlopeOpen W))).map
      (infinityOutputRestriction W).toRingHom =
      W.map (algebraMap R (InfinityAdditionOpen W)) := by
    ext <;> exact (infinityOutputRestriction W).commutes _
  rw [he] at h
  exact h

/-- The regular addition algebra map on this neighborhood of the infinity pair. -/
def infinityAdditionChart : Coordinate W 1 →ₐ[R] InfinityAdditionOpen W :=
  evaluation W 1
    (infinityOutputInverse W • (infinityOutputRestriction W ∘ infinityOutputCoordinates W))
    (((W.map (algebraMap R (InfinityAdditionOpen W))).toProjective.equation_smul _
      (Units.isUnit _)).mpr (infinityRestrictedOutput_equation W))
    (infinityOutputInverse_mul W)

/-- The regular chart map is the explicit normalized infinity addition formula. -/
@[simp] theorem infinityAdditionChart_coord (i : Fin 3) :
    infinityAdditionChart W (coord W 1 i) =
      infinityOutputInverse W * infinityOutputRestriction W (infinityOutputCoordinates W i) :=
  evaluation_coord W 1 _ _ _ i

/-- Clearing output Y recovers the integral formula from the actual chart morphism. -/
theorem infinityAdditionChart_mul (i : Fin 3) :
    infinityAdditionChart W (coord W 1 i) *
      infinityOutputRestriction W (infinityOutputCoordinates W 1) =
      infinityOutputRestriction W (infinityOutputCoordinates W i) := by
  rw [infinityAdditionChart_coord]
  linear_combination
    infinityOutputRestriction W (infinityOutputCoordinates W i) * infinityOutputInverse_mul W

end FLT.Mazur.WeierstrassIntegralChart
