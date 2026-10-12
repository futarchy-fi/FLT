/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianCanonicalSheafClassification
public import FLT.Mazur.GrassmannianSheafQuotientComparison
public import FLT.Mazur.ModuleSheafLocalFrames

/-!
# Faithful classification of full original sheaf quotients

Two actual locally free ambient quotients classify identically exactly when
their entire projections are isomorphic. The compatible isomorphism is unique.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P Q : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P) [Epi p]
  (q : grassmannianSchemeAmbient (M := M) β ⟶ Q)
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The original epimorphism determines a projection-preserving isomorphism uniquely. -/
theorem sheafQuotientIso_unique (e e' : P ≅ Q)
    (he : p ≫ e.hom = q) (he' : p ≫ e'.hom = q) : e = e' := by
  apply Iso.ext
  exact (cancel_epi p).mp (he.trans he'.symm)

/-- A common classification constructs the unique full quotient isomorphism. -/
theorem SheafQuotientClassifies.existsUnique_iso
    {f : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f)
    (h' : SheafQuotientClassifies β q b hκ f) :
    ∃! e : P ≅ Q, p ≫ e.hom = q := by
  obtain ⟨e, he⟩ := h.exists_iso β p q b hκ h'
  exact ⟨e, he, fun e' he' ↦ sheafQuotientIso_unique β p q e' e he' he⟩

variable [Epi q] {τ σ : Type u} [Fintype τ] [Fintype σ]
  (hP : ModuleSheafLocalFrames.HasFrames τ P) (hd : Fintype.card τ = d)
  (hQ : ModuleSheafLocalFrames.HasFrames σ Q) (hd' : Fintype.card σ = d)

/-- Equality of actual classifying maps is exactly full quotient isomorphism. -/
theorem locallyFreeQuotientClassifyingMap_eq_iff_iso :
    locallyFreeQuotientClassifyingMap β p b hκ hP hd =
      locallyFreeQuotientClassifyingMap β q b hκ hQ hd' ↔
      ∃ e : P ≅ Q, p ≫ e.hom = q := by
  constructor
  · intro h
    have hp := locallyFreeQuotientClassifyingMap_spec β p b hκ hP hd
    rw [h] at hp
    exact hp.exists_iso β p q b hκ
      (locallyFreeQuotientClassifyingMap_spec β q b hκ hQ hd')
  · rintro ⟨e, he⟩
    exact locallyFreeQuotientClassifyingMap_iso β p b hκ hP hd q hQ hd' e he

end FLT.Mazur.GrassmannianChart
