/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCommonRefinement

/-!
# Common principal covers of individual relative chart transitions

A point belongs to a relative transition exactly when its image in the
changed-base scheme lies in the smaller chart. Thus common principal
refinements also cover each transition source, with actual lifts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Membership in a transition is detected after the chart open immersion. -/
lemma relativeTensorTransition_mem_range_iff {U V : X.affineOpens} (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    ∀ x : Spec (.of (RelativeAlgebra J f V)),
      x ∈ Set.range (relativeTensorTransition J f i) ↔
        relativeTensorChart J f V x ∈ Set.range (relativeTensorChart J f U) := by
  intro _ _ x
  let _ := relativeTensorChart_isOpenImmersion J f V
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    exact (congrArg (fun g ↦ g y) (relativeTensorTransition_chart J f i)).symm
  · rintro ⟨y, hy⟩
    refine ⟨y, (relativeTensorChart J f V).isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun g ↦ g y) (relativeTensorTransition_chart J f i)).trans hy

/-- Common principal refinements cover the source of every original relative transition. -/
lemma relativeTensorTransition_exists_common_principal {U V : X.affineOpens}
    (i : U.1 ⟶ V.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    ∀ x : Spec (.of (RelativeAlgebra J f U)),
      ∃ (r : Γ(X, U.1)) (s : Γ(X, V.1)),
        X.basicOpen r = X.basicOpen s ∧
        let W : X.affineOpens := ⟨X.basicOpen r, U.2.basicOpen r⟩
        let := closedBaseAlgebra J f W.1
        x ∈ Set.range (relativeTensorTransition J f (U := W) (V := U)
          (homOfLE (X.basicOpen_le r))) := by
  intro _ _ x
  have hxV : relativeTensorChart J f U x ∈ Set.range (relativeTensorChart J f V) := by
    refine ⟨relativeTensorTransition J f i x, ?_⟩
    exact congrArg (fun g ↦ g x) (relativeTensorTransition_chart J f i)
  obtain ⟨r, s, hrs, hx⟩ := relativeTensorChart_exists_common_principal J f U V
    (relativeTensorChart J f U x) ⟨x, rfl⟩ hxV
  refine ⟨r, s, hrs, ?_⟩
  exact (relativeTensorTransition_mem_range_iff J f
    (U := ⟨X.basicOpen r, U.2.basicOpen r⟩) (V := U) (homOfLE (X.basicOpen_le r)) x).mpr hx

end FLT.Mazur.IdealAdicGradedPullback
