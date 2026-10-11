/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericH1
public import FLT.Mazur.PolygonCompleteZeroParameterFiber
public import FLT.Mazur.StructureCohomologyOverIso

/-!
# Actual H1 on every field fiber of the complete polygon family

A field-valued coefficient map either kills the original parameter, giving
the original polygon, or makes it regular, giving flat coefficient base change.
Both cases compute actual H1, including for every specified cartesian square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A field-valued coefficient map not killing the parameter is flat. -/
theorem completeCoefficient_flat_of_parameter_ne_zero
    (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0) :
    a.Flat := by
  let _ := a.toAlgebra
  apply PowerSeriesParameterFlatness.flat K L
  intro x hx
  change a PowerSeries.X * x = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left ha

/-- Every actual field-valued coefficient fiber has H1 of dimension one. -/
theorem completeCoefficientFiberH1_finrank (L : Type) [Field L]
    (a : PowerSeries K →+* L) :
    Module.finrank L (H1 (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom a)))) = 1 := by
  by_cases ha : a PowerSeries.X = 0
  · obtain ⟨u, v, huv⟩ := completeZeroParameterFiber_exists_cocone K n h L a ha _ _
      (IsPullback.of_hasPullback _ _)
    have hp := PolygonCohomologyIncidence.h1_finrank L n (by omega) u v huv
    exact hp
  · let _ : Flat (Spec.map (CommRingCat.ofHom a)) :=
      Flat.SpecMap_iff.mpr (completeCoefficient_flat_of_parameter_ne_zero K L a ha)
    exact completeFlatFieldH1_finrank K n h L _

/-- Every original field point gives actual first cohomology of dimension one. -/
theorem completeFieldFiberH1_finrank (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K))) :
    Module.finrank L (H1 (pullback.snd (exactVeroneseProjToBase K n h) s)) = 1 := by
  have he := completeCoefficientFiberH1_finrank K n h L (Spec.preimage s).hom
  rwa [show Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s from
    Spec.map_preimage s] at he

/-- The computation holds on the original structure map of every specified fiber square. -/
theorem completeCartesianFieldH1_finrank (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (exactVeroneseProjToBase K n h) s) :
    Module.finrank L (H1 q) = 1 := by
  have he := structureScalarH_finrank_of_overIso hs.isoPullback
    (pullback.snd (exactVeroneseProjToBase K n h) s) q hs.isoPullback_hom_snd 1
  exact he.symm.trans (completeFieldFiberH1_finrank K n h L s)

end FLT.Mazur.PolygonInfinitesimalStages
