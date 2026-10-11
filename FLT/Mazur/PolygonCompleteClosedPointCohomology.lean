/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointHZero
public import FLT.Mazur.PolygonCompletePointPowerComparison
public import FLT.Mazur.PolygonCompletePointPowerVanishing

/-!
# Exact single-point cohomology on the original closed polygon

Transfer the computed polygon H0 through the original complete coefficient
comparison. The closed Cartesian point powers have h0=m and vanishing H1
for positive m. No generic-fiber base-change assertion is made here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original complete point coefficient has the exact positive H0 dimension on the polygon. -/
theorem completePointPower_closed_h0 (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Module.finrank K (ModuleScalarH (PolygonCyclicAtlas.toBase K n h)
      ((Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj
        (tensorPower (completePointLine K n h i) m)) 0) = m := by
  exact ((moduleScalarHFunctor (PolygonCyclicAtlas.toBase K n h) 0).mapIso
    (completePointPowerClosedIso K n h i m)).toLinearEquiv.finrank_eq.trans
      (PolygonSinglePointHZero.finrank K n (by omega) _ _
        (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i m hm)

/-- The closed Cartesian single-point power has the same exact H0 dimension. -/
theorem completeCartesianPointLine_closed_h0 (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Module.finrank K (ModuleScalarH (PolygonCyclicAtlas.toBase K n h)
      (tensorPower (completeCartesianPointLine K n h (completeClosedBase K)
        (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
        (completeClosedFiber_isPullback K n h) i) m) 0) = m := by
  exact ((moduleScalarHFunctor (PolygonCyclicAtlas.toBase K n h) 0).mapIso
    (completeCartesianPointPowerIso K n h (completeClosedBase K) _ _
      (completeClosedFiber_isPullback K n h) i m)).toLinearEquiv.finrank_eq.symm.trans
        (completePointPower_closed_h0 K n h i m hm)

/-- Every positive closed Cartesian single-point power has vanishing first cohomology. -/
theorem completeCartesianPointLine_closed_h1 (i : Fin n) (m : ℕ) :
    Subsingleton (ModuleScalarH (PolygonCyclicAtlas.toBase K n h)
      (tensorPower (completeCartesianPointLine K n h (completeClosedBase K)
        (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
        (completeClosedFiber_isPullback K n h) i) (m + 1)) 1) :=
  completeCartesianPointLine_positive_h1_of_first K n h K (completeClosedBase K) _ _
    (completeClosedFiber_isPullback K n h) i
    (completeCartesianPointLine_closed_h0 K n h i 1 (by decide)) m

/-- Vanishing also holds for the actual closed pullback of the original complete coefficient. -/
theorem completePointPower_closed_h1 (i : Fin n) (m : ℕ) :
    Subsingleton (ModuleScalarH (PolygonCyclicAtlas.toBase K n h)
      ((Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj
        (tensorPower (completePointLine K n h i) (m + 1))) 1) := by
  exact (Equiv.subsingleton_congr
    ((moduleScalarHFunctor (PolygonCyclicAtlas.toBase K n h) 1).mapIso
      (completeCartesianPointPowerIso K n h (completeClosedBase K) _ _
        (completeClosedFiber_isPullback K n h) i (m + 1))).toLinearEquiv.toEquiv).mpr
          (completeCartesianPointLine_closed_h1 K n h i m)

end FLT.Mazur.PolygonInfinitesimalStages
