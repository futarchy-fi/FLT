/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProjectiveRelationNormNeighborhood
public import FLT.Mazur.RelativeRelationNormPrincipal

/-!
# Original invariant-sheaf principal neighborhoods from finite-projective sections

Locally constructed norms supply scalars in the actual equalizer sheaf.
No global free basis of the original relation is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Module
namespace FLT.Mazur.RelativeRelationOrbit
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

variable [IsAffine A.left] [IsAffine D.left] [LocallyQuasiFinite p.left]
  (es : CategoryTheory.EquivalenceRelation p.left q.left)

include es in
/-- Whole-relation norms construct a principal neighborhood in every original orbit open. -/
theorem exists_invariantPrincipal_of_finite_projective (W O : Opens (Orbit e)) (hOW : O ≤ W)
    (x : Orbit e) (hx : x ∈ O) :
    let _ := p.left.appTop.hom.toAlgebra
    Module.Finite Γ(A.left, ⊤) Γ(D.left, ⊤) →
    Module.Projective Γ(A.left, ⊤) Γ(D.left, ⊤) →
      ∃ s : (invariantSheaf e).obj.obj (op W),
        x ∈ invariantPrincipal e W s ∧ invariantPrincipal e W s ≤ O := by
  let _ := p.left.appTop.hom.toAlgebra
  dsimp only
  intro hf hp
  obtain ⟨a, rfl⟩ := projection_surjective e x
  obtain ⟨s, hs, ha, hU⟩ :=
    AffineLocallyFreeRelationNorm.exists_invariant_principal_of_finite_projective
    p.left q.left es (pullOpen e O).val a (fun z hz ↦ by
      change projection e (q.left z) ∈ O
      rw [← projection_pair e z, hz]
      exact hx) hf hp
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
