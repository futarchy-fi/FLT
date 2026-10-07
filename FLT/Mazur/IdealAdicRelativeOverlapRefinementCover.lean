/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapCover

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

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- An overlap point lies in a refinement chart exactly when its base point does. -/
lemma relativeTensorOverlapChart_mem_range_iff {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (x : relativeTensorOverlap J f U V) :
    x ∈ Set.range (relativeTensorOverlapChart J f i j) ↔
      (Limits.pullback.fst (relativeTensorChart J f U) (relativeTensorChart J f V) ≫
        relativeTensorChart J f U) x ∈ Set.range (relativeTensorChart J f W) := by
  let _ := relativeTensorChart_isOpenImmersion J f U
  let _ := relativeTensorChart_isOpenImmersion J f V
  let p := Limits.pullback.fst (relativeTensorChart J f U) (relativeTensorChart J f V)
  have hc : relativeTensorOverlapChart J f i j ≫ p ≫ relativeTensorChart J f U =
      relativeTensorChart J f W := by
    rw [relativeTensorOverlapChart_fst_assoc, relativeTensorTransition_chart]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (congrArg (fun g ↦ g z) hc).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply p.isOpenEmbedding.injective
    apply (relativeTensorChart J f U).isOpenEmbedding.injective
    exact (congrArg (fun g ↦ g z) hc).trans hz

/-- Intersections of overlap-chart images have common affine refinements at every point. -/
lemma relativeTensorOverlapChart_exists_refinement {U V W T : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (a : T.1 ⟶ U.1) (b : T.1 ⟶ V.1)
    (x : relativeTensorOverlap J f U V)
    (hxW : x ∈ Set.range (relativeTensorOverlapChart J f i j))
    (hxT : x ∈ Set.range (relativeTensorOverlapChart J f a b)) :
    ∃ (Z : X.affineOpens) (k : Z.1 ⟶ W.1) (_l : Z.1 ⟶ T.1),
      x ∈ Set.range (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j)) := by
  let y := (Limits.pullback.fst (relativeTensorChart J f U) (relativeTensorChart J f V) ≫
    relativeTensorChart J f U) x
  obtain ⟨r, s, hrs, hz⟩ := relativeTensorChart_exists_common_principal J f W T y
    ((relativeTensorOverlapChart_mem_range_iff J f i j x).mp hxW)
    ((relativeTensorOverlapChart_mem_range_iff J f a b x).mp hxT)
  let Z : X.affineOpens := ⟨X.basicOpen r, W.2.basicOpen r⟩
  let k : Z.1 ⟶ W.1 := homOfLE (X.basicOpen_le r)
  let l : Z.1 ⟶ T.1 := homOfLE (by
    change X.basicOpen r ≤ T.1
    rw [hrs]
    exact X.basicOpen_le s)
  exact ⟨Z, k, l, (relativeTensorOverlapChart_mem_range_iff J f (k ≫ i) (k ≫ j) x).mpr hz⟩

/-- Every common refinement has the same map to the overlap through either ambient chart. -/
lemma relativeTensorOverlapChart_common_refinement {U V W T Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (a : T.1 ⟶ U.1) (b : T.1 ⟶ V.1)
    (k : Z.1 ⟶ W.1) (l : Z.1 ⟶ T.1) :
    relativeTensorTransition J f k ≫ relativeTensorOverlapChart J f i j =
      relativeTensorTransition J f l ≫ relativeTensorOverlapChart J f a b := by
  rw [relativeTensorOverlapChart_refine, relativeTensorOverlapChart_refine]
  congr 1

end FLT.Mazur.IdealAdicGradedPullback
