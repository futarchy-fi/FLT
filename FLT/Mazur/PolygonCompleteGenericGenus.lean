/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFieldH1
public import FLT.Mazur.PolygonCompleteGenericPureDimension
public import FLT.Mazur.PolygonCompleteConstantSections

/-!
# Genus one of the actual geometric generic fibers

The original fiber's proved dimension, constant functions and actual H1
computation give genus one, for every extension of the original fraction field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (F L : Type) [Field F] [Field L] [Algebra (PowerSeries K) F]
  [IsFractionRing (PowerSeries K) F] [Algebra F L] [Algebra (PowerSeries K) L]
  [IsScalarTower (PowerSeries K) F L]

/-- Every actual geometric generic fiber has genus one for its original structure morphism. -/
theorem completeGeometricGenericFiber_genus :
    let _ := exactVeroneseProjToBase_isProper K n h
    let s := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))
    curveGenus (pullback.snd (exactVeroneseProjToBase K n h) s)
      (completeGeometricGenericFiber_dimension K n h F L)
      (completeFieldFiber_constantSections K n h L s) = 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact completeGeometricGenericH1_finrank K n h F L

end FLT.Mazur.PolygonInfinitesimalStages
