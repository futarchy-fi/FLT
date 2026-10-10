/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapProjections

/-!
# Common affine charts in triple relative intersections

Every point belonging to three relative charts has a common ambient affine
refinement. This supplies the pointwise cover needed to detect the cocycle.
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

/-- Every point in a triple chart intersection has a common affine refinement. -/
lemma relativeTensorChart_exists_triple_refinement (U V T : X.affineOpens)
    (x : relativeScheme J f)
    (hU : x ∈ Set.range (relativeTensorChart J f U))
    (hV : x ∈ Set.range (relativeTensorChart J f V))
    (hT : x ∈ Set.range (relativeTensorChart J f T)) :
    ∃ (W : X.affineOpens) (_i : W.1 ⟶ U.1) (_j : W.1 ⟶ V.1) (_k : W.1 ⟶ T.1),
      x ∈ Set.range (relativeTensorChart J f W) := by
  let z := (J.comap f).subschemeι (relativeSchemeToClosed J f x)
  have hz : z ∈ (U.1 ⊓ V.1 ⊓ T.1 : X.Opens) :=
    ⟨⟨(relativeTensorChart_mem_range_iff J f U x).mp hU,
      (relativeTensorChart_mem_range_iff J f V x).mp hV⟩,
      (relativeTensorChart_mem_range_iff J f T x).mp hT⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hsub : W ≤ U.1 ⊓ V.1 ⊓ T.1⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz (U.1 ⊓ V.1 ⊓ T.1).2
  exact ⟨⟨W, hW⟩, homOfLE (hsub.trans (inf_le_left.trans inf_le_left)),
    homOfLE (hsub.trans (inf_le_left.trans inf_le_right)), homOfLE (hsub.trans inf_le_right),
    (relativeTensorChart_mem_range_iff J f ⟨W, hW⟩ x).mpr hzW⟩

end FLT.Mazur.IdealAdicGradedPullback
