/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericPureDimension
public import FLT.Mazur.PolygonCompleteGeometricallyConnected
public import FLT.Mazur.DRFiberClassification

/-!
# Classified fibers of the original complete polygon family

The original parameter distinguishes polygon fibers from smooth relative curves.
The existing geometry supplies the full nodal core on every specified field square.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.CurveFiberHypotheses FCurve.DRFiberClassification

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual nonzero-parameter fiber square is a smooth relative curve. -/
theorem completeCartesianField_relativeDimension (L : Type) [Field L]
    (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom a))) : SmoothOfRelativeDimension 1 q := by
  let _ := a.toAlgebra
  let _ := completeBaseChange_relativeDimension_of_parameter_isUnit K n h L
    (isUnit_iff_ne_zero.mpr ha)
  rw [← hs.isoPullback_hom_snd]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1)
    inferInstance hs.isoPullback.hom

/-- Every specified field fiber is classified, with all of its original nodal geometry. -/
theorem completeCartesianField_classified (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hs : IsPullback p q (exactVeroneseProjToBase K n h) s) :
    ClassifiedFiberCore q := by
  let a := (Spec.preimage s).hom
  have he : Spec.map (CommRingCat.ofHom a) = s := Spec.map_preimage s
  have hs' : IsPullback p q (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom a)) := he.symm ▸ hs
  by_cases ha : a PowerSeries.X = 0
  · obtain ⟨u, v, huv⟩ := completeZeroParameterFiber_exists_cocone K n h L a ha p q hs'
    exact ⟨PolygonNodalCore.nodalFiberCore L n (by omega) u v huv,
      Or.inr ⟨n, by omega, u, v, huv⟩⟩
  · let _ := exactVeroneseProjToBase_isProper K n h
    let _ := exactVeroneseProjToBase_geometricallyConnected K n h
    let _ := exactVeroneseProjToBase_geometricallyReduced K n h
    let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
    let _ := completeCartesianField_relativeDimension K n h L a ha p q hs'
    let _ := SmoothOfRelativeDimension.smooth 1 q
    let _ : ConnectedSpace Y :=
      GeometricallyConnected.geometrically_connectedSpace _ _ _ hs
    let _ : IsReduced Y := GeometricallyReduced.geometrically_isReduced _ _ _ hs
    let _ := Chow.source_isNoetherian q
    exact ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance,
      smoothCurvePureDimension q, nodes_of_smoothFiber q⟩, Or.inl inferInstance⟩

/-- The original complete family has classified geometric fibers. -/
theorem exactVeroneseProjToBase_classifiedGeometricFibers :
    ClassifiedGeometricFibers (exactVeroneseProjToBase K n h) :=
  ⟨fun L _ _ s _ p q hs ↦ completeCartesianField_classified K n h L s p q hs⟩

end FLT.Mazur.PolygonInfinitesimalStages
