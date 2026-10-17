/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTargetInvariantPrincipalCore
public import FLT.Mazur.SchemeFiniteTargetFiber
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import FLT.Mazur.EquivalenceRelationFiniteTargetSaturation

/-!
# Constructed invariant affine neighborhoods in the finite target locus

Prime avoidance puts a whole finite orbit in one principal domain. Its norm
core is affine and invariant. In particular, the saturated finite target
locus has enough invariant affine refinements inside any prescribed orbit open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  [IsAffine A.left] [Flat p.left] [LocallyOfFinitePresentation p.left]

include e in
/-- A whole finite orbit in a finite target domain has an actual invariant affine neighborhood. -/
theorem exists_invariant_affine_of_wholeFiber (W : A.left.Opens) (x : A.left)
    (hW : ∀ z : D.left, p.left z = x → q.left z ∈ W)
    (hf : ∀ z : D.left, p.left z = x → q.left z ∈ finiteTargetOpen p.left) :
    ∃ U : InvariantOpens p q, IsAffineOpen U.val ∧ x ∈ U.val ∧
      U.val ≤ W ∧ U.val ≤ finiteTargetOpen p.left := by
  have hx : x ∈ finiteTargetOpen p.left := by
    obtain ⟨z, hp, hq⟩ := related_refl e x
    exact hq ▸ hf z hp
  obtain ⟨s, hs, hsW⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (W ⊓ finiteTargetOpen p.left) (q.left '' (p.left ⁻¹' {x}))
    ((finite_fiber_of_mem_finiteTarget p.left x hx).image q.left) (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨hW z hz, hf z hz⟩)
  have hsf := hsW.trans inf_le_right
  refine ⟨⟨finitePrincipalCore (q := q) s hsf,
    finitePrincipalCore_preimage_eq e s hsf⟩, finitePrincipalCore_isAffine s hsf, ?_,
    (finitePrincipalCore_le s hsf).trans (hsW.trans inf_le_left),
    (finitePrincipalCore_le s hsf).trans hsf⟩
  exact (mem_finitePrincipalCore_iff e s hsf x).mpr fun z hz ↦ hs ⟨z, hz, rfl⟩

variable (es : CategoryTheory.EquivalenceRelation p.left q.left)
  [LocallyQuasiFinite p.left] [IsSeparated p.left]
  [Flat q.left] [LocallyOfFinitePresentation q.left]

include e es in
/-- Every finite-locus point has invariant affine refinements inside each original orbit open. -/
theorem exists_invariant_affine_of_finiteTarget (W : InvariantOpens p q) (x : A.left)
    (hx : x ∈ W.val) (hf : x ∈ finiteTargetOpen p.left) :
    ∃ U : InvariantOpens p q, IsAffineOpen U.val ∧ x ∈ U.val ∧
      U.val ≤ W.val ∧ U.val ≤ finiteTargetOpen p.left := by
  apply exists_invariant_affine_of_wholeFiber e W.val x
  · intro z hz
    exact (invariant_mem_iff W ⟨z, hz, rfl⟩).mp hx
  · exact EquivalenceRelationFiber.finiteTargetOpen_fullFiber es x hf

end FLT.Mazur.RelativeRelationOrbit
