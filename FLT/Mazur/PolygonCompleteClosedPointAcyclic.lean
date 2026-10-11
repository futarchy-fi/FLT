/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedPointCohomology
public import FLT.Mazur.PolygonHigherStructureCohomology
public import FLT.Mazur.DivisorPowerHigherVanishing

/-!
# All positive cohomology of the original closed point powers

Higher structure vanishing propagates through the actual finite marked
divisor. Together with the computed H1 this makes every positive point power
on the original closed square acyclic in all positive degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every original closed Cartesian point power has no cohomology above degree one. -/
theorem completeCartesianPointLine_closed_higher (i : Fin n) (m r : ℕ) :
    Subsingleton (ModuleScalarH (PolygonCyclicAtlas.toBase K n h)
      (tensorPower (completeCartesianPointLine K n h (completeClosedBase K)
        (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
        (completeClosedFiber_isPullback K n h) i) m) (r + 2)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper (PolygonCyclicAtlas.toBase K n h) :=
    MorphismProperty.of_isPullback (completeClosedFiber_isPullback K n h) inferInstance
  let _ := completeCartesianPoint_isFinite K n h K (completeClosedBase K) _ _
    (completeClosedFiber_isPullback K n h) i
  let _ : Subsingleton (ModuleScalarH (PolygonCyclicAtlas.toBase K n h)
      (structureModule (PolygonCyclicAtlas.scheme K n h)) (r + 2)) :=
    PolygonHigherStructureCohomology.higher_subsingleton K n (by omega)
      (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
      (PolygonCyclicPushout.isPushout K n h (by omega)) r
  exact divisorPower_positive_subsingleton (PolygonCyclicAtlas.toBase K n h)
    (completeCartesianMarking_relativeCartier K n h (completeClosedBase K) _ _
      (completeClosedFiber_isPullback K n h) i).1 (r + 2) (by omega) m

/-- Positive complete point powers have positive-acyclic original closed pullbacks. -/
theorem completePointPower_closed_positive (i : Fin n) (m r : ℕ) :
    Subsingleton (ModuleH
      ((Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj
        (tensorPower (completePointLine K n h i) (m + 1))) (r + 1)) := by
  cases r with
  | zero => exact completePointPower_closed_h1 K n h i m
  | succ r =>
    exact (Equiv.subsingleton_congr
      ((moduleScalarHFunctor (PolygonCyclicAtlas.toBase K n h) (r + 2)).mapIso
      (completeCartesianPointPowerIso K n h (completeClosedBase K) _ _
        (completeClosedFiber_isPullback K n h) i (m + 1))).toLinearEquiv.toEquiv).mpr
        (completeCartesianPointLine_closed_higher K n h i (m + 1) r)

end FLT.Mazur.PolygonInfinitesimalStages
