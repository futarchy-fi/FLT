/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericRelativeDimension
public import FLT.Mazur.PolygonCompleteGeometricGenericFiber
public import FLT.Mazur.SmoothCurvePureDimension

/-!
# Dimension and pure dimension of actual geometric generic fibers

Every field extension of the original fraction field has a nonempty relative
curve as its actual fiber. Its noetherian irreducible components all have
dimension one; the assertion is stronger than whole-space dimension alone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (F L : Type) [Field F] [Field L] [Algebra (PowerSeries K) F]
  [IsFractionRing (PowerSeries K) F] [Algebra F L] [Algebra (PowerSeries K) L]
  [IsScalarTower (PowerSeries K) F L]

include F in
/-- Every actual geometric generic fiber has relative dimension one. -/
theorem completeGeometricGenericFiber_relativeDimension :
    SmoothOfRelativeDimension 1 (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L)))) := by
  apply completeBaseChange_relativeDimension_of_parameter_isUnit
  rw [IsScalarTower.algebraMap_apply (PowerSeries K) F L]
  apply IsUnit.map
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    (IsFractionRing.injective (PowerSeries K) F).ne PowerSeries.X_ne_zero

include F in
/-- The whole actual geometric generic fiber has topological dimension one. -/
theorem completeGeometricGenericFiber_dimension :
    topologicalKrullDim ↥(pullback (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L)))) = 1 := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))
  exact FCurve.smoothCurveDimension (pullback.snd (exactVeroneseProjToBase K n h) g)
    (completeGeometricGenericFiber_relativeDimension K n h F L)
    (completeFiber_nonempty K n h g)

include F in
/-- Every irreducible component of every actual geometric generic fiber has dimension one. -/
theorem completeGeometricGenericFiber_pureDimension :
    FCurve.CurveFiberHypotheses.PureDimensionOne
      (pullback (exactVeroneseProjToBase K n h)
        (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := completeGeometricGenericFiber_relativeDimension K n h F L
  let _ := Chow.source_isNoetherian (pullback.snd (exactVeroneseProjToBase K n h) g)
  exact FCurve.smoothCurvePureDimension (pullback.snd (exactVeroneseProjToBase K n h) g)

end FLT.Mazur.PolygonInfinitesimalStages
