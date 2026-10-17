/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRelationNormNeighborhood
public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.RelativeRelationInvariantPrincipal

/-!
# Principal neighborhoods in the actual invariant sheaf from relation norms

The whole original finite-free relation supplies invariant principal
neighborhoods inside every orbit open. The scalar is a section of the actual
equalizer sheaf and restricts to the requested original domain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Module
namespace FLT.Mazur.RelativeRelationOrbit
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- An invariant original global function determines a section of the actual equalizer sheaf. -/
def globalInvariantSection (s : Γ(A.left, ⊤)) (hs : p.left.appTop s = q.left.appTop s) :
    (invariantSheaf e).obj.obj (op ⊤) :=
  (invariantSectionRingEquiv e ⊤).symm ⟨s, by
    change p.left.appTop s = q.left.appLE ⊤ ⊤ _ s
    simpa [Scheme.Hom.appLE] using hs⟩

/-- The constructed invariant section recovers the original function literally. -/
theorem globalInvariantSection_val (s : Γ(A.left, ⊤))
    (hs : p.left.appTop s = q.left.appTop s) :
    (invariantInclusion e).hom.app (op ⊤) (globalInvariantSection e s hs) = s := by
  exact congrArg Subtype.val ((invariantSectionRingEquiv e ⊤).apply_symm_apply ⟨s, _⟩)

/-- Its unit locus is tested on the unchanged original source. -/
theorem projection_mem_globalInvariantSection (s : Γ(A.left, ⊤))
    (hs : p.left.appTop s = q.left.appTop s) (x : A.left) :
    projection e x ∈ invariantPrincipal e ⊤ (globalInvariantSection e s hs) ↔
      x ∈ A.left.basicOpen s := by
  change x ∈ (pullOpen e (invariantPrincipal e ⊤ (globalInvariantSection e s hs))).val ↔ _
  rw [pullOpen_invariantPrincipal, globalInvariantSection_val]

/-- Restricting a global invariant scalar intersects its principal open with the domain. -/
theorem invariantPrincipal_restrict_top (W : Opens (Orbit e))
    (s : (invariantSheaf e).obj.obj (op ⊤)) :
    invariantPrincipal e W ((invariantSheaf e).obj.map (homOfLE le_top).op s) =
      W ⊓ invariantPrincipal e ⊤ s :=
  RingedSpace.basicOpen_res (ringedSpace e) (homOfLE le_top).op s

variable [IsAffine A.left] [IsAffine D.left] [LocallyQuasiFinite p.left]
  (es : CategoryTheory.EquivalenceRelation p.left q.left)

include es in
/-- Whole-relation norms construct a principal neighborhood in every original orbit open. -/
theorem exists_invariantPrincipal_of_basis (W O : Opens (Orbit e)) (hOW : O ≤ W)
    (x : Orbit e) (hx : x ∈ O) {ι : Type v} [Finite ι] :
    let _ := p.left.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A.left, ⊤) Γ(D.left, ⊤)),
      ∃ s : (invariantSheaf e).obj.obj (op W),
        x ∈ invariantPrincipal e W s ∧ invariantPrincipal e W s ≤ O := by
  let _ := p.left.appTop.hom.toAlgebra
  dsimp only
  intro basis
  obtain ⟨a, rfl⟩ := projection_surjective e x
  obtain ⟨s, hs, ha, hU⟩ := AffineRelationNorm.exists_invariant_principal
    p.left q.left es (pullOpen e O).val a (fun z hz ↦ by
      change projection e (q.left z) ∈ O
      rw [← projection_pair e z, hz]
      exact hx) basis
  let t := globalInvariantSection e s hs
  have ht : invariantPrincipal e ⊤ t ≤ O := by
    intro y hy
    obtain ⟨b, rfl⟩ := projection_surjective e y
    exact hU ((projection_mem_globalInvariantSection e s hs b).mp hy)
  refine ⟨(invariantSheaf e).obj.map (homOfLE le_top).op t, ?_, ?_⟩
  · rw [invariantPrincipal_restrict_top]
    exact ⟨hOW hx, (projection_mem_globalInvariantSection e s hs a).mpr ha⟩
  · rw [invariantPrincipal_restrict_top]
    exact inf_le_right.trans ht

end FLT.Mazur.RelativeRelationOrbit
