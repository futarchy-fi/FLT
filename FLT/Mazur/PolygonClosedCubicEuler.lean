/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveStructureEuler
public import FLT.Mazur.PolygonClosedCubicContractionFinite
public import FLT.Mazur.PolygonGenusOne
public import FLT.Mazur.WeierstrassGenusOneFamily

/-!
# Equal structure Euler characteristics for the original closed comparison

The actual one-gon and the specified Cartesian closed cubic both have
one-dimensional H0 and H1. Their structure Euler characteristics therefore
agree, including at the singularities; no smoothness hypothesis is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i

/-- The actual contracted one-gon has zero structure Euler characteristic. -/
theorem closedPointOneGon_euler_zero :
    curveEulerCharacteristic (PolygonAtlas.polygon K 1).hom
      (structureModule (PolygonAtlas.polygon K 1).left) = 0 := by
  apply curveEulerCharacteristic_structure_zero
  · exact finrank_H0_of_constantGlobalSections _
      (PolygonConstantSections.constants K 1 (by decide)
        (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
        (PolygonAtlas.isPushout K 1 (by decide)))
  · exact PolygonCohomologyIncidence.h1_finrank K 1 (by decide)
      (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
      (PolygonAtlas.isPushout K 1 (by decide))

/-- The specified original Cartesian closed cubic has zero structure Euler characteristic. -/
theorem closedPointCubic_euler_zero :
    curveEulerCharacteristic (closedPointCubicOver K n h i).hom
      (structureModule (closedPointCubicOver K n h i).left) = 0 := by
  apply curveEulerCharacteristic_structure_zero
  · exact integralCurveFieldSquareH0_finrank W
      (completeClosedBase K ≫ (Spec (.of (PowerSeries K))).toSpecΓ)
      (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
  · exact integralCurveFieldSquareH1_finrank W
      (completeClosedBase K ≫ (Spec (.of (PowerSeries K))).toSpecΓ)
      (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)

/-- The original global comparison preserves the structure Euler characteristic. -/
theorem closedPointContractionComparison_euler :
    curveEulerCharacteristic
      ((closedPointContractionComparison K n h i).left ≫ (closedPointCubicOver K n h i).hom)
      (structureModule (PolygonAtlas.polygon K 1).left) =
    curveEulerCharacteristic (closedPointCubicOver K n h i).hom
      (structureModule (closedPointCubicOver K n h i).left) := by
  rw [Over.w, closedPointOneGon_euler_zero, closedPointCubic_euler_zero]

end FLT.Mazur.PolygonInfinitesimalStages
