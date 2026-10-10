/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineNegation
public import FLT.Mazur.WeierstrassProjectiveChartProduct

/-!
# Regular negation near infinity

Invert the negated Y coordinate on the Y chart and normalize the negated
homogeneous point. The resulting algebra map is defined on an explicit open
neighborhood containing the entire zero section over the coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The output Y coordinate before normalization. -/
def infinityNegationDen : Coordinate W 1 := chartNegationCoordinates W 1 1

/-- Negation has Y-chart output on this explicit principal open. -/
abbrev InfinityNegationOpen := Localization.Away (infinityNegationDen W)

/-- Restriction of the original Y chart to the negation neighborhood. -/
def infinityNegationRestriction : Coordinate W 1 →ₐ[R] InfinityNegationOpen W :=
  IsScalarTower.toAlgHom R _ _

/-- The output coordinate becomes invertible on its prescribed domain. -/
theorem infinityNegationDen_isUnit :
    IsUnit (infinityNegationRestriction W (infinityNegationDen W)) :=
  IsLocalization.Away.algebraMap_isUnit (infinityNegationDen W)

/-- The chosen reciprocal of the homogeneous output Y coordinate. -/
def infinityNegationInverse : InfinityNegationOpen W :=
  ↑(infinityNegationDen_isUnit W).unit⁻¹

/-- The reciprocal cancels the homogeneous output Y coordinate. -/
@[simp] theorem infinityNegationInverse_mul :
    infinityNegationInverse W * infinityNegationRestriction W (infinityNegationDen W) = 1 :=
  Units.inv_mul_eq_one.mpr (infinityNegationDen_isUnit W).unit_spec

/-- Restricted homogeneous negation still satisfies the cubic. -/
theorem infinityNegation_equation :
    (W.map (algebraMap R (InfinityNegationOpen W))).toProjective.Equation
      (infinityNegationRestriction W ∘ chartNegationCoordinates W 1) := by
  change (W.map (algebraMap R (InfinityNegationOpen W))).toProjective.Equation
    (algebraMap (Coordinate W 1) (InfinityNegationOpen W) ∘ chartNegationCoordinates W 1)
  have h := (chartNegationCoordinates_equation W 1).map
    (algebraMap (Coordinate W 1) (InfinityNegationOpen W))
  simpa only [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R
    (Coordinate W 1) (InfinityNegationOpen W)] using h

/-- The normalized regular negation morphism into the Y chart. -/
def infinityNegationChart : Coordinate W 1 →ₐ[R] InfinityNegationOpen W :=
  evaluation W 1
    (infinityNegationInverse W •
      (infinityNegationRestriction W ∘ chartNegationCoordinates W 1))
    (((W.map (algebraMap R (InfinityNegationOpen W))).toProjective.equation_smul _
      (Units.isUnit _)).mpr (infinityNegation_equation W))
    (infinityNegationInverse_mul W)

/-- Normalized output coordinates of the infinity negation map. -/
@[simp] theorem infinityNegationChart_coord (i : Fin 3) :
    infinityNegationChart W (coord W 1 i) = infinityNegationInverse W *
      infinityNegationRestriction W (chartNegationCoordinates W 1 i) :=
  evaluation_coord W 1 _ _ _ i

/-- The defining denominator is minus one along the entire zero section. -/
theorem infinityNegationDen_zero :
    chartInfinityEvaluation (S := R) W (infinityNegationDen W) = -1 := by
  simp [infinityNegationDen, chartNegationCoordinates, Projective.negY, AlgHom.commutes]

/-- The zero section lifts to the whole infinity negation neighborhood. -/
def infinityNegationZero : InfinityNegationOpen W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityNegationDen W)
    (show IsUnit (chartInfinityEvaluation (S := R) W (infinityNegationDen W)) by
      rw [infinityNegationDen_zero]
      exact isUnit_neg_one)

/-- The lifted zero section restricts to the original zero section. -/
theorem infinityNegationZero_restriction :
    (infinityNegationZero W).comp (infinityNegationRestriction W) =
      chartInfinityEvaluation W := by
  apply AlgHom.ext
  intro a
  change infinityNegationZero W (algebraMap _ _ a) = _
  simp only [infinityNegationZero, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- Normalization is minus one at zero. -/
theorem infinityNegationZero_inverse :
    infinityNegationZero W (infinityNegationInverse W) = -1 := by
  have h := congrArg (infinityNegationZero W) (infinityNegationInverse_mul W)
  rw [map_mul, map_one] at h
  have hd := DFunLike.congr_fun (infinityNegationZero_restriction W) (infinityNegationDen W)
  change infinityNegationZero W (infinityNegationRestriction W (infinityNegationDen W)) = _
    at hd
  rw [hd, infinityNegationDen_zero] at h
  linear_combination -h

/-- The actual normalized negation map fixes the zero section. -/
theorem infinityNegationZero_chart :
    (infinityNegationZero W).comp (infinityNegationChart W) = chartInfinityEvaluation W := by
  apply hom_ext
  intro i
  change infinityNegationZero W (infinityNegationChart W (coord W 1 i)) = _
  rw [infinityNegationChart_coord, map_mul, infinityNegationZero_inverse]
  have h := DFunLike.congr_fun (infinityNegationZero_restriction W)
    (chartNegationCoordinates W 1 i)
  change infinityNegationZero W (infinityNegationRestriction W _) = _ at h
  rw [h]
  fin_cases i <;>
    simp [chartNegationCoordinates, Projective.negY, AlgHom.commutes]

end FLT.Mazur.WeierstrassIntegralChart
