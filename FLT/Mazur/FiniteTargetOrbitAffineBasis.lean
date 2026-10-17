/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTargetInvariantAffineNeighborhood

/-!
# Actual orbit neighborhoods with finite affine source domains

The constructed invariant affine cores descend to the original orbit space.
They refine every prescribed original orbit open at a finite-locus point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (es : CategoryTheory.EquivalenceRelation p.left q.left)
  [IsAffine A.left] [Flat p.left] [LocallyOfFinitePresentation p.left]
  [LocallyQuasiFinite p.left] [IsSeparated p.left]
  [Flat q.left] [LocallyOfFinitePresentation q.left]

include es in
/-- Finite-locus points have actual quotient neighborhoods with finite affine source. -/
theorem exists_finite_affine_orbit_neighborhood
    (W : TopologicalSpace.Opens (Orbit e)) (x : A.left)
    (hx : projection e x ∈ W) (hf : x ∈ finiteTargetOpen p.left) :
    ∃ Z : TopologicalSpace.Opens (Orbit e), projection e x ∈ Z ∧ Z ≤ W ∧
      IsAffineOpen (pullOpen e Z).val ∧ (pullOpen e Z).val ≤ finiteTargetOpen p.left := by
  obtain ⟨U, ha, hxU, hUW, hUf⟩ :=
    exists_invariant_affine_of_finiteTarget e es (pullOpen e W) x hx hf
  refine ⟨descendOpen e U, ⟨x, hxU, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hUW hy
  · rwa [pullOpen_descendOpen]
  · rwa [pullOpen_descendOpen]

include es in
/-- Every orbit open inside the finite locus is covered by finite affine source domains. -/
theorem finite_affine_orbit_cover (W : TopologicalSpace.Opens (Orbit e))
    (hf : (pullOpen e W).val ≤ finiteTargetOpen p.left) :
    (⨆ (Z : TopologicalSpace.Opens (Orbit e)) (_ : Z ≤ W)
      (_ : IsAffineOpen (pullOpen e Z).val), Z) = W := by
  apply le_antisymm
  · exact iSup_le fun Z ↦ iSup_le fun hZ ↦ iSup_le fun _ ↦ hZ
  · intro y hy
    obtain ⟨x, rfl⟩ := projection_surjective e y
    obtain ⟨Z, hxZ, hZW, ha, _⟩ :=
      exists_finite_affine_orbit_neighborhood e es W x hy (hf hy)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨Z,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨hZW,
        TopologicalSpace.Opens.mem_iSup.mpr ⟨ha, hxZ⟩⟩⟩

end FLT.Mazur.RelativeRelationOrbit
