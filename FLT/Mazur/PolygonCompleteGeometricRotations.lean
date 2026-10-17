/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraphCartesian
public import FLT.Mazur.PolygonCompleteClosedActionComparison
public import FLT.Mazur.PolygonCompleteClassifiedFibers
public import FLT.Mazur.PolygonGeneralizedCurve

/-!
# Geometric graph rotations of the original complete polygon action

Every singular field fiber kills the original parameter and hence factors
through the actual closed polygon. Its full action comparison transports all
components, nodes and translations, proving the DR geometric graph condition.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "X" => completeOriginalWholeOver K n h

/-- Every singular actual field fiber factors through the original closed coefficient map. -/
theorem completeSingularField_factor (L : Type) [Field L]
    (g : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
    (hs : ¬ Smooth ((Over.pullback g).obj (X)).hom) :
    ∃ t : Spec (.of L) ⟶ Spec (.of K), t ≫ completeClosedBase K = g := by
  let a := (Spec.preimage g).hom
  have he : Spec.map (CommRingCat.ofHom a) = g := Spec.map_preimage g
  have ha : a PowerSeries.X = 0 := by
    by_contra ha
    have hp' : IsPullback (pullback.fst (X).hom g) (pullback.snd (X).hom g)
        (exactVeroneseProjToBase K n h) (Spec.map (CommRingCat.ofHom a)) := by
      rw [he]
      exact IsPullback.of_hasPullback _ _
    let _ := completeCartesianField_relativeDimension K n h L a ha _ _ hp'
    apply hs
    change Smooth (pullback.snd (X).hom g)
    exact SmoothOfRelativeDimension.smooth 1 _
  refine ⟨Spec.map (CommRingCat.ofHom (a.comp PowerSeries.C)), ?_⟩
  rw [completeClosedBase, ← Spec.map_comp, ← he]
  congr 1
  exact CommRingCat.hom_ext (completeCoefficient_factor K L a ha).symm

/-- The whole original action rotates the actual graph on every singular geometric fiber. -/
theorem completeWholeAction_geometricRotations :
    let _ : LocallyOfFinitePresentation (X).hom := exactVeroneseProjToBase_lfp K n h
    GeneralizedCurveGraph.GeometricRotations (completeWholeAction K n h) := by
  let _ : LocallyOfFinitePresentation (X).hom := exactVeroneseProjToBase_lfp K n h
  let _ : LocallyOfFinitePresentation (C).hom := PolygonPinching.polygon_lfp K n hn P Q hp
  change GeneralizedCurveGraph.GeometricRotations (completeWholeAction K n h)
  intro L _ _ g hs
  obtain ⟨t, ht⟩ := completeSingularField_factor K n h L g hs
  let _ := (Spec.preimage t).hom.toAlgebra
  have he : ProjectiveLineProductCharts.parameterToBase K L = t := Spec.map_preimage t
  have hr : GeneralizedCurveGraph.FiberRotations
      (PolygonUniversalAction.act K n hn P Q hp) t := by
    rw [← he]
    exact PolygonGeneralizedCurve.field_rotations K n hn P Q hp L
  rw [← ht]
  exact GeneralizedCurveGraph.fiberRotations_of_cartesian (completeClosedBase K)
    (completeClosedGroupPullbackIso K n h) (completeClosedWholePullbackIso K n h)
    (completeWholeAction K n h) (PolygonUniversalAction.act K n hn P Q hp)
    (completeClosedPullback_action K n h) t hr

end FLT.Mazur.PolygonInfinitesimalStages
