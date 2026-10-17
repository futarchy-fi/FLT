/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRelationNorm
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Original invariant principal neighborhoods from whole-relation norms

Prime avoidance first chooses a function nonvanishing on every endpoint in
the original finite orbit. Its whole-relation norm is invariant and its
principal open stays inside the prescribed original open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineRelationNorm
universe u v
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  (e : CategoryTheory.EquivalenceRelation p q) {ι : Type v} [Finite ι]

/-- The original norm tests every second endpoint of the entire first-projection fiber. -/
theorem mem_basicOpen_relationNorm_iff :
    let _ := p.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)) (x : A),
      x ∈ A.basicOpen (relationNorm p q s) ↔
        ∀ z : D, p z = x → q z ∈ A.basicOpen s := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s x
  rw [relationNorm, sectionNorm, AffineSectionNormFiber.mem_basicOpen_norm_iff p basis]
  rw [← Scheme.preimage_basicOpen_top q s]
  rfl

include e in
/-- Reflexivity makes the norm principal open smaller than the original principal open. -/
theorem basicOpen_relationNorm_le :
    let _ := p.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)),
      A.basicOpen (relationNorm p q s) ≤ A.basicOpen s := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s x hx
  have hp : p (e.r x) = x := by
    exact congrArg (fun h : A ⟶ A ↦ h x) e.reflexivity₁
  have hq : q (e.r x) = x := by
    exact congrArg (fun h : A ⟶ A ↦ h x) e.reflexivity₂
  have h := (mem_basicOpen_relationNorm_iff p q basis s x).mp hx (e.r x) hp
  rwa [hq] at h

include e in
/-- An entire finite original orbit inside an open has an invariant principal neighborhood. -/
theorem exists_invariant_principal_of_finite_fiber (U : A.Opens) (x : A)
    (hf : (p ⁻¹' {x}).Finite) (hU : ∀ z : D, p z = x → q z ∈ U) :
    let _ := p.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)),
      ∃ s : Γ(A, ⊤), p.appTop s = q.appTop s ∧
        x ∈ A.basicOpen s ∧ A.basicOpen s ≤ U := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis
  obtain ⟨s, hs, hsU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    U (q '' (p ⁻¹' {x})) (hf.image q) (by
      rintro _ ⟨z, hz, rfl⟩
      exact hU z hz)
  refine ⟨relationNorm p q s, relationNorm_invariant p q e basis s, ?_,
    (basicOpen_relationNorm_le p q e basis s).trans hsU⟩
  apply (mem_basicOpen_relationNorm_iff p q basis s x).mpr
  intro z hz
  exact hs ⟨z, hz, rfl⟩

include e in
/-- Quasi-finite affine projections supply the finite orbit without a chosen enumeration. -/
theorem exists_invariant_principal [LocallyQuasiFinite p] (U : A.Opens) (x : A)
    (hU : ∀ z : D, p z = x → q z ∈ U) :
    let _ := p.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)),
      ∃ s : Γ(A, ⊤), p.appTop s = q.appTop s ∧
        x ∈ A.basicOpen s ∧ A.basicOpen s ≤ U :=
  exists_invariant_principal_of_finite_fiber p q e U x
    (p.finite_preimage_singleton x) hU

end FLT.Mazur.AffineRelationNorm
