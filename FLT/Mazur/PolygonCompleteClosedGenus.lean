/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiber
public import FLT.Mazur.PolygonCyclicPushout
public import FLT.Mazur.PolygonClassifiedFamily

/-!
# Polygon classification and genus of the actual complete closed fiber

The original polygon comparison transports its pinching cocone to the actual
closed fiber. The established polygon cohomology computation gives genus one,
including after arbitrary extension of its residue field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original polygon comparison as an isomorphism over the residue-field base. -/
def completeClosedPolygonIso : PolygonCyclicAtlas.polygon K n h ≅
    Over.mk (pullback.snd (exactVeroneseProjToBase K n h) (completeClosedBase K)) :=
  Over.isoMk (completeClosedFiberIso K n h) (completeClosedFiberIso_snd K n h)

/-- The complete closed fiber has the original polygon's actual pinching presentation. -/
theorem completeClosedFiber_exists_cocone :
    ∃ (a : PolygonPinching.components K n ⟶
        Over.mk (pullback.snd (exactVeroneseProjToBase K n h) (completeClosedBase K)))
      (b : PolygonPinching.nodes K n ⟶
        Over.mk (pullback.snd (exactVeroneseProjToBase K n h) (completeClosedBase K))),
      IsPushout (PolygonPinching.toComponents K n (by omega))
        (PolygonPinching.toNodes K n) a b := by
  let e := completeClosedPolygonIso K n h
  exact ⟨PolygonCyclicAtlas.normalization K n h ≫ e.hom,
    PolygonCyclicAtlas.nodes K n h ≫ e.hom,
    (PolygonCyclicPushout.isPushout K n h (by omega)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simp) (by simp)⟩

/-- The actual complete closed fiber is a classified genus-one family over its residue field. -/
theorem completeClosedFiber_classifiedGenusOne :
    ClassifiedGenusOneFamily
      (pullback.snd (exactVeroneseProjToBase K n h) (completeClosedBase K)) := by
  obtain ⟨a, b, hp⟩ := completeClosedFiber_exists_cocone K n h
  exact PolygonClassifiedFamily.family K n (by omega) a b hp

/-- Every base change of that same complete closed fiber retains classification and genus one. -/
theorem completeClosedFiber_baseChange_classifiedGenusOne {S : Scheme}
    (s : S ⟶ Spec (.of K)) :
    ClassifiedGenusOneFamily (pullback.snd
      (pullback.snd (exactVeroneseProjToBase K n h) (completeClosedBase K)) s) :=
  (completeClosedFiber_classifiedGenusOne K n h).baseChange s

end FLT.Mazur.PolygonInfinitesimalStages
