/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicOmittedConstant
public import FLT.Mazur.PolygonOneGonContractionDescent
public import FLT.Mazur.PolygonClosedCubicContractionComparison

/-!
# The original closed cubic map factors through the actual one-gon contraction

Descend the retained complete normalization map and the common original node
morphism through the original one-gon pushout. The resulting global comparison
preserves the original marking and extends the existing identity-open comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)

/-- The specified Cartesian closed cubic with its actual coefficient morphism. -/
def closedPointCubicOver : Over (Spec (.of K)) :=
  Over.mk (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure (completePointWeierstrassCurve K n h i))
    (completeClosedBase K ≫ (Spec (.of (PowerSeries K))).toSpecΓ))

/-- The original cubic comparison as a morphism over the original residue field. -/
def closedPointToCubicOver : PolygonCyclicAtlas.polygon K n h ⟶ closedPointCubicOver K n h i :=
  Over.homMk (closedPointToCubic K n h i)
    (completePointToCubicBaseChange_snd K n h (completeClosedBase K)
      (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
      (completeClosedFiber_isPullback K n h) i)

/-- Omitted complete components are constant with their coefficient morphisms retained. -/
theorem closedPointToCubicOver_omitted (j : Fin n) (hj : j ≠ i) :
    componentι K n j ≫ p ≫ closedPointToCubicOver K n h i =
      componentToPoint K ≫ ProjectiveLine.zeroSection K ≫
        componentι K n j ≫ p ≫ closedPointToCubicOver K n h i := by
  apply Over.OverMorphism.ext
  exact closedPointOmitted_constant K n h i hj

/-- The constructed global map from the original contracted one-gon to the closed cubic. -/
def closedPointContractionComparison :
    PolygonAtlas.polygon K 1 ⟶ closedPointCubicOver K n h i :=
  PolygonOneGonContractionDescent.desc K n (by omega) p q hp
    (closedPointToCubicOver K n h i) i (closedPointToCubicOver_omitted K n h i)

/-- The entire original cubic map factors through the actual component contraction. -/
@[reassoc] theorem closedPointContractionComparison_fac :
    closedPointContraction K n h i ≫ (closedPointContractionComparison K n h i).left =
      closedPointToCubic K n h i :=
  congrArg Over.Hom.left (PolygonOneGonContractionDescent.contraction_desc K n
    (by omega) p q hp (closedPointToCubicOver K n h i) i
    (closedPointToCubicOver_omitted K n h i))

/-- The full retained component has exactly the original cubic morphism. -/
@[reassoc] theorem closedPointContractionComparison_retained :
    (retainedComponent K).left ≫ (closedPointContractionComparison K n h i).left =
      closedPointComponentToCubic K n h i i :=
  congrArg Over.Hom.left (PolygonOneGonContractionDescent.retained_desc K n
    (by omega) p q hp (closedPointToCubicOver K n h i) i
    (closedPointToCubicOver_omitted K n h i))

/-- The global comparison preserves the unchanged original unit-one marking. -/
@[reassoc] theorem closedPointContractionComparison_marking :
    PolygonMarkedSections.sectionMap K 1 (PolygonAtlas.normalization K 1) 1 0 ≫
      (closedPointContractionComparison K n h i).left =
        completePointCubicChangedZero K n h (completeClosedBase K) i := by
  have H := closedPointCommonIdentityMarking_toOneGon K n h i
  rw [← H, Category.assoc, closedPointOneGonIdentityInclusion, Category.assoc,
    closedPointContractionComparison_fac]
  exact closedPointCommonIdentityMarking_toCubic K n h i

/-- On the common identity open, the global map is the already constructed local comparison. -/
@[reassoc] theorem closedPointContractionComparison_identity :
    closedPointOneGonIdentityInclusion K n h i ≫
      (closedPointContractionComparison K n h i).left =
        closedPointCubicIdentityInclusion K n h i := by
  rw [closedPointOneGonIdentityInclusion, Category.assoc, closedPointContractionComparison_fac]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
