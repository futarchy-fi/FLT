/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGeometricallyReduced
public import FLT.Mazur.LocalClosedFiberConnectedness

/-!
# Geometric connectedness of the actual complete polygon family

The original polygon controls the closed point. The original proper flat
pointed family has geometrically reduced fibers, so the local closed-fiber
comparison proves geometric connectedness of the whole complete family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open Approximation

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original polygon is geometrically connected over its actual residue field. -/
theorem completeOriginalPolygon_geometricallyConnected :
    GeometricallyConnected (PolygonCyclicAtlas.toBase K n h) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ s ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := PolygonFieldExtension.exists_cocone_of_isPullback K L n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) s _ _
    (IsPullback.of_hasPullback _ _)
  exact PolygonConnected.connected L n (by omega) u v huv

/-- The original closed base point belongs to the actual connected-fiber locus. -/
theorem completeClosedPoint_mem_connectedLocus :
    IsLocalRing.closedPoint (PowerSeries K) ∈
      geometricallyConnectedLocus (exactVeroneseProjToBase K n h) := by
  let _ := completeOriginalPolygon_geometricallyConnected K n h
  apply range_subset_geometricallyConnectedLocus (completeClosedFiber_isPullback K n h)
  rw [completeClosedBase_range]
  exact Set.mem_singleton _

/-- The actual original complete family has geometrically connected fibers everywhere. -/
theorem exactVeroneseProjToBase_geometricallyConnected :
    GeometricallyConnected (exactVeroneseProjToBase K n h) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := exactVeroneseProjToBase_flat K n h
  let _ := exactVeroneseProjToBase_geometricallyReduced K n h
  exact geometricallyConnected_of_spec_local_closedFiber (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h ⟨0, by omega⟩) (completeBaseMarking_toBase K n h _)
    (completeClosedPoint_mem_connectedLocus K n h)

/-- Every actual field fiber, including every geometric generic fiber, is connected. -/
theorem completeFieldFiber_connected (L : Type) [Field L]
    (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K))) :
    ConnectedSpace ↥(pullback (exactVeroneseProjToBase K n h) s) := by
  let _ := exactVeroneseProjToBase_geometricallyConnected K n h
  exact GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)

end FLT.Mazur.PolygonInfinitesimalStages
