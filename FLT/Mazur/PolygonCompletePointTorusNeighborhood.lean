/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicTorus
public import FLT.Mazur.PolygonCompletePointGlobalFunctions
public import FLT.Mazur.PolygonCompletePrincipalClosedFiber
public import FLT.Mazur.ProperFunctionSheafIso

/-!
# The original contraction is unchanged near every retained closed torus point

Finite fibers of the actual closed contraction give finite fibers of the
whole complete-base map. Its original function maps then give genuine open
isomorphism neighborhoods, including all generizations of those points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- The actual inclusion of the original closed cubic into the complete-base cubic. -/
def completePointCubicClosedInclusion :
    (closedPointCubicOver K n h i).left ⟶ integralCurve (W) :=
  pullback.fst (integralCurveStructure (W)) (completeClosedBase K ≫ (S₀).toSpecΓ)

instance completePointCubicClosedInclusion_closed :
    IsClosedImmersion (completePointCubicClosedInclusion K n h i) := by
  unfold completePointCubicClosedInclusion
  infer_instance

/-- Every retained closed torus point has a finite fiber in the full original family. -/
theorem completePointToIntegralCubic_finite_fiber_closedTorus
    (y : (closedPointCubicOver K n h i).left)
    (hy : y ∈ (closedPointCubicTorus K n h i).opensRange) :
    ((g) ⁻¹' {completePointCubicClosedInclusion K n h i y}).Finite := by
  apply CartesianFiniteFibers.finite_fiber
    (completePointToCubicBaseChange_isPullback K n h (completeClosedBase K)
      (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
      (completeClosedFiber_isPullback K n h) i)
    (completePointCubicClosedInclusion K n h i).isClosedEmbedding.injective
  exact closedPointCubicTorus_finite_fiber K n h i y hy

/-- Every original closed torus point has an unchanged neighborhood in the entire cubic. -/
theorem completePointToIntegralCubic_exists_isIso_closedTorus
    (y : (closedPointCubicOver K n h i).left)
    (hy : y ∈ (closedPointCubicTorus K n h i).opensRange) :
    ∃ U : (integralCurve (W)).Opens,
      completePointCubicClosedInclusion K n h i y ∈ U ∧ IsIso ((g) ∣_ U) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact ProperFunctionSheafIso.exists_isIso_neighborhood (g)
    (completePointToIntegralCubic_app_isIso K n h i) _
    (completePointToIntegralCubic_finite_fiber_closedTorus K n h i y hy)

end FLT.Mazur.PolygonInfinitesimalStages
