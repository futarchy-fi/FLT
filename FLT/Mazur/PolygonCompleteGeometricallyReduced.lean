/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteZeroParameterFiber
public import FLT.Mazur.PolygonCompleteGeometricGenericFiber

/-!
# Geometric reducedness of the actual complete polygon family

Every field-valued coefficient map either kills the original parameter or
makes it invertible. The first fiber is the original reduced polygon; the
second is smooth over the field. These cover all actual field fibers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every field-valued coefficient change of the original complete family is reduced. -/
theorem completeFieldFiber_isReduced (L : Type) [Field L] (a : PowerSeries K →+* L) :
    IsReduced (pullback (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom a))) := by
  by_cases ha : a PowerSeries.X = 0
  · obtain ⟨u, v, huv⟩ := completeZeroParameterFiber_exists_cocone K n h L a ha _ _
      (IsPullback.of_hasPullback _ _)
    exact (PolygonNodalCore.nodalFiberCore L n (by omega) u v huv).reduced
  · let _ := a.toAlgebra
    let _ := completeBaseChange_smooth_of_parameter_isUnit K n h L
      (isUnit_iff_ne_zero.mpr ha)
    exact Approximation.isReduced_of_smooth_field (pullback.snd _ _)

/-- The actual original structure map has geometrically reduced fibers everywhere. -/
theorem exactVeroneseProjToBase_geometricallyReduced :
    GeometricallyReduced (exactVeroneseProjToBase K n h) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ s ↦ ?_⟩
  have hr := completeFieldFiber_isReduced K n h L (Spec.preimage s).hom
  rwa [show Spec.map (CommRingCat.ofHom (Spec.preimage s).hom) = s from
    Spec.map_preimage s] at hr

/-- Flatness over the original reduced power-series base also makes the total space reduced. -/
theorem exactVeroneseProj_isReduced : IsReduced (exactVeroneseProj K n h) := by
  let _ := exactVeroneseProjToBase_flat K n h
  let _ := exactVeroneseProjToBase_geometricallyReduced K n h
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (exactVeroneseProjToBase K n h)

end FLT.Mazur.PolygonInfinitesimalStages
