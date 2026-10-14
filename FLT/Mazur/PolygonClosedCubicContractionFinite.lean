/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveFinite
public import FLT.Mazur.OneGonIntegral
public import FLT.Mazur.PolygonDimension
public import FLT.Mazur.PolygonClosedCubicNonconstant

/-!
# Finiteness of the original one-gon comparison

The actual source is a proper integral curve of dimension one. The original
marking and omitted component have distinct images, so the comparison is finite.
This controls the node fiber as well as the already unchanged identity open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "a" => closedPointContractionComparison K n h i

/-- The global comparison is finite on the whole original one-gon. -/
theorem closedPointContractionComparison_finite : IsFinite (a).left := by
  let _ := PolygonProper.proper K 1 (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide))
  let _ : IsSeparated (closedPointCubicOver K n h i).hom := by
    change IsSeparated (CategoryTheory.Limits.pullback.snd
      (WeierstrassIntegralChart.integralCurveStructure
        (completePointWeierstrassCurve K n h i)) _)
    infer_instance
  let _ : IsIntegral (PolygonAtlas.polygon K 1).left := OneGonIntegral.integral K
  exact FCurve.nonconstantProperCurveFinite (PolygonAtlas.polygon K 1).hom
    (closedPointCubicOver K n h i).hom (a).left inferInstance inferInstance
    (PolygonDimension.atlas K 1).le inferInstance (Over.w (a))
    (closedPointContractionComparison_nonconstant K n h i)

/-- Every original target point, including the node image, has a finite preimage. -/
theorem closedPointContractionComparison_finite_fiber
    (y : (closedPointCubicOver K n h i).left) :
    ((a).left ⁻¹' {y}).Finite := by
  let _ := closedPointContractionComparison_finite K n h i
  exact (a).left.finite_preimage_singleton y

end FLT.Mazur.PolygonInfinitesimalStages
