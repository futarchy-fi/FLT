/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjPositiveBasis
public import FLT.Mazur.SectionGradedProjOpens

/-!
# An open canonical Proj immersion implies ampleness

A positive homogeneous basic neighborhood contained in the open image pulls
back to an affine generator open. These neighborhoods give the section-open
definition of ampleness without assuming a projective embedding.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjAmpleOfOpenImmersion
open FCurve SectionGradedSum SectionGradedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} [CompactSpace X] (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- An open immersion into the full section-ring Proj certifies section-open ampleness. -/
lemma ample (h : PositivePowerGenerated L) [IsOpenImmersion (toProj L h)] :
    AmpleLineBundle L := by
  refine ⟨inferInstance, hL.out, fun x ↦ ?_⟩
  obtain ⟨n, a, hn, ha, hx, hU⟩ := GradedProjPositiveBasis.exists_basicOpen_le (grade L ⊤)
    (U := (toProj L h).opensRange) (x := toProj L h x) ⟨x, rfl⟩
  obtain ⟨s, rfl⟩ := ha
  have hp := SectionGradedProjOpens.toProj_preimage_basicOpen L h s hn
  refine ⟨n, hn, s, ?_, ?_⟩
  · rw [← hp]
    exact hx
  · rw [← hp]
    exact (Proj.isAffineOpen_basicOpen (grade L ⊤) (of L ⊤ n s)
      (show of L ⊤ n s ∈ grade L ⊤ n from ⟨s, rfl⟩) hn).preimage_of_isOpenImmersion
        (toProj L h) hU

end FLT.Mazur.SectionGradedProjAmpleOfOpenImmersion
