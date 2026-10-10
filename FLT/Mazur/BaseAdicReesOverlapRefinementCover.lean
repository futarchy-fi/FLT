/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesOverlapCover

/-!
# Common refinements inside full relative overlaps

Membership in an overlap chart is detected in the changed-base scheme.
The intersection of two such chart images is covered by charts refining
both ambient affine opens. These are the covers needed to check gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

/-- An overlap point lies in a refinement chart exactly when its base point does. -/
lemma modelOverlapChart_mem_range_iff {U V W : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (x : modelOverlap f J U V) :
    x ∈ Set.range (modelOverlapChart f J i j) ↔
      (Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V) ≫
        chartSpaceMap f J U) x ∈ Set.range (chartSpaceMap f J W) := by
  let _ := chartSpaceMap_isOpenImmersion f J U
  let _ := chartSpaceMap_isOpenImmersion f J V
  let p := Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V)
  have hc : modelOverlapChart f J i j ≫ p ≫ chartSpaceMap f J U =
      chartSpaceMap f J W := by
    rw [modelOverlapChart_fst_assoc]
    exact relativeRingRestriction_spec f J i
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (congrArg (fun g ↦ g z) hc).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply p.isOpenEmbedding.injective
    apply (chartSpaceMap f J U).isOpenEmbedding.injective
    exact (congrArg (fun g ↦ g z) hc).trans hz

/-- Intersections of overlap-chart images have common affine refinements at every point. -/
lemma modelOverlapChart_exists_refinement {U V W T : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (a : T.1 ≤ U.1) (b : T.1 ≤ V.1)
    (x : modelOverlap f J U V)
    (hxW : x ∈ Set.range (modelOverlapChart f J i j))
    (hxT : x ∈ Set.range (modelOverlapChart f J a b)) :
    ∃ (Z : X.affineOpens) (k : Z.1 ≤ W.1) (_l : Z.1 ≤ T.1),
      x ∈ Set.range (modelOverlapChart f J (k.trans i) (k.trans j)) := by
  let y := (Limits.pullback.fst (chartSpaceMap f J U) (chartSpaceMap f J V) ≫
    chartSpaceMap f J U) x
  obtain ⟨r, s, hrs, hz⟩ := chartSpaceMap_exists_common_principal f J W T y
    ((modelOverlapChart_mem_range_iff f J i j x).mp hxW)
    ((modelOverlapChart_mem_range_iff f J a b x).mp hxT)
  let Z : X.affineOpens := ⟨X.basicOpen r, W.2.basicOpen r⟩
  let k : Z.1 ≤ W.1 := X.basicOpen_le r
  let l : Z.1 ≤ T.1 := by
    change X.basicOpen r ≤ T.1
    rw [hrs]
    exact X.basicOpen_le s
  exact ⟨Z, k, l, (modelOverlapChart_mem_range_iff f J (k.trans i) (k.trans j) x).mpr hz⟩

/-- Every common refinement has the same map to the overlap through either ambient chart. -/
lemma modelOverlapChart_common_refinement {U V W T Z : X.affineOpens}
    (i : W.1 ≤ U.1) (j : W.1 ≤ V.1) (a : T.1 ≤ U.1) (b : T.1 ≤ V.1)
    (k : Z.1 ≤ W.1) (l : Z.1 ≤ T.1) :
    modelMap f J k ≫ modelOverlapChart f J i j =
      modelMap f J l ≫ modelOverlapChart f J a b := by
  rw [modelOverlapChart_refine, modelOverlapChart_refine]

end FLT.Mazur.BaseAdicRees
