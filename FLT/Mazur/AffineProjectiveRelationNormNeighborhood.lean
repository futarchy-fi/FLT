/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeRelationNorm
public import FLT.Mazur.FiniteProjectiveAffineNorm
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Invariant principal neighborhoods without a global relation basis

The full-orbit prime avoidance argument uses the norm glued from actual local
bases. Finite projectivity constructs those bases, without assuming the local
charts are invariant or replacing the original relation by an envelope.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineLocallyFreeRelationNorm
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Reflexivity bounds the principal open of the locally constructed norm. -/
theorem basicOpen_relationNorm_le (s : Γ(A, ⊤)) :
    A.basicOpen (relationNorm p q U hU hcover s) ≤ A.basicOpen s := by
  intro x hx
  have hp : p (e.r x) = x := congrArg (fun h : A ⟶ A ↦ h x) e.reflexivity₁
  have hq : q (e.r x) = x := congrArg (fun h : A ⟶ A ↦ h x) e.reflexivity₂
  have h := (mem_basicOpen_relationNorm_iff p q U hU hcover s x).mp hx (e.r x) hp
  rwa [hq] at h

include e U hU hcover in
/-- A full finite orbit in an open yields an original invariant principal neighborhood. -/
theorem exists_invariant_principal_of_finite_fiber (W : A.Opens) (x : A)
    (hf : (p ⁻¹' {x}).Finite) (hW : ∀ z : D, p z = x → q z ∈ W) :
    ∃ s : Γ(A, ⊤), p.appTop s = q.appTop s ∧
      x ∈ A.basicOpen s ∧ A.basicOpen s ≤ W := by
  obtain ⟨s, hs, hsW⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    W (q '' (p ⁻¹' {x})) (hf.image q) (by
      rintro _ ⟨z, hz, rfl⟩
      exact hW z hz)
  refine ⟨relationNorm p q U hU hcover s, relationNorm_invariant p q U hU hcover e s,
    ?_, (basicOpen_relationNorm_le p q U hU hcover e s).trans hsW⟩
  apply (mem_basicOpen_relationNorm_iff p q U hU hcover s x).mpr
  intro z hz
  exact hs ⟨z, hz, rfl⟩

include e in
/-- Finite projectivity of the original section algebra replaces a chosen global finite basis. -/
theorem exists_invariant_principal_of_finite_projective [LocallyQuasiFinite p]
    (W : A.Opens) (x : A) (hW : ∀ z : D, p z = x → q z ∈ W) :
    let _ := p.appTop.hom.toAlgebra
    Module.Finite Γ(A, ⊤) Γ(D, ⊤) → Module.Projective Γ(A, ⊤) Γ(D, ⊤) →
    ∃ s : Γ(A, ⊤), p.appTop s = q.appTop s ∧
      x ∈ A.basicOpen s ∧ A.basicOpen s ≤ W := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro hf hp
  exact exists_invariant_principal_of_finite_fiber p q
    (FiniteProjectiveAffineNorm.chart p hf hp) (FiniteProjectiveAffineNorm.chart_basis p hf hp)
    (FiniteProjectiveAffineNorm.chart_cover p hf hp) e W x (p.finite_preimage_singleton x) hW

end FLT.Mazur.AffineLocallyFreeRelationNorm
