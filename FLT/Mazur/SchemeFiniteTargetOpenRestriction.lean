/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteTargetRestriction

/-!
# The exact finite target locus commutes with open restriction

Finite neighborhoods on an original open domain are precisely restrictions
of original finite neighborhoods. The reverse inclusion uses the whole
restricted morphism, transported through the actual restriction isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p : D ⟶ A)

/-- The intrinsic finite target locus is unchanged by restricting to an open domain. -/
theorem finiteTargetOpen_restrict (B : A.Opens) :
    finiteTargetOpen (p ∣_ B) = B.ι ⁻¹ᵁ finiteTargetOpen p := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hU, hxU⟩ := (mem_finiteTargetOpen (p ∣_ B) x).mp hx
    have hf : IsFinite (p ∣_ B.ι ''ᵁ U) :=
      (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
        (morphismRestrictRestrict p B U)).mp hU
    exact (mem_finiteTargetOpen p (B.ι x)).mpr ⟨B.ι ''ᵁ U, hf, ⟨x, hxU, rfl⟩⟩
  · exact preimage_finiteTargetOpen_le (isPullback_morphismRestrict p B).flip

/-- Restricting to the exact finite target locus leaves no further finite-locus obstruction. -/
theorem finiteTargetOpen_restrict_finiteTarget :
    finiteTargetOpen (p ∣_ finiteTargetOpen p) = ⊤ := by
  let _ := finite_restrict_finiteTarget p
  exact finiteTargetOpen_eq_top _

end FLT.Mazur.SchemeOpenEnvelope
