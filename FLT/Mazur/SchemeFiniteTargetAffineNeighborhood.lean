/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteTargetBaseChange

/-!
# Affine neighborhoods inside the exact finite target locus

A finite target neighborhood can be shrunk inside any prescribed open while
retaining finiteness of the whole preimage. Its source is then affine too.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p : D ⟶ A)

/-- Finiteness of the full restricted map survives shrinking the target open. -/
theorem finite_restrict_of_le {U V : A.Opens} (h : U ≤ V) [IsFinite (p ∣_ V)] :
    IsFinite (p ∣_ U) := by
  have H : IsPullback (p ∣_ U) (D.homOfLE (p.preimage_mono h))
      (A.homOfLE h) (p ∣_ V) := by
    refine .of_bot ?_ (morphismRestrict_homOfLE p U V h)
      (isPullback_morphismRestrict p V)
    simpa using isPullback_morphismRestrict p U
  exact MorphismProperty.of_isPullback H.flip inferInstance

/-- Finite target points have whole-preimage finite affine neighborhoods inside any open. -/
theorem exists_finite_affine_target (x : A) (hx : x ∈ finiteTargetOpen p)
    (O : A.Opens) (hxO : x ∈ O) :
    ∃ U : A.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧ IsFinite (p ∣_ U.1) := by
  obtain ⟨V, hV, hxV⟩ := (mem_finiteTargetOpen p x).mp hx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V ⊓ O from ⟨hxV, hxO⟩)
  let _ := hV
  exact ⟨⟨U, hU⟩, hxU, hUV.trans inf_le_right,
    finite_restrict_of_le p (hUV.trans inf_le_left)⟩

/-- An affine test loses none of the original finite target locus. -/
theorem mem_finiteTargetOpen_iff_affine (x : A) :
    x ∈ finiteTargetOpen p ↔
      ∃ U : A.affineOpens, x ∈ U.1 ∧ IsFinite (p ∣_ U.1) := by
  constructor
  · intro hx
    obtain ⟨U, hxU, _, hU⟩ := exists_finite_affine_target p x hx ⊤ (by trivial)
    exact ⟨U, hxU, hU⟩
  · rintro ⟨U, hxU, hU⟩
    exact (mem_finiteTargetOpen p x).mpr ⟨U.1, hU, hxU⟩

end FLT.Mazur.SchemeOpenEnvelope
