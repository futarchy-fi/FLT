/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionBaseLocalization
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.SectionGeneratorScalar

/-!
# Extending sections from a principal open

On a quasi-compact separated scheme, a section of a quasi-coherent module on
a principal open has a global numerator. Multiplication by one further power
controls its nonvanishing locus outside that principal open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open Chow
variable {X : Scheme} (M : X.Modules)

/-- Invertible sheaves are finitely presented, with no finiteness assumption on the base. -/
theorem LocallyFreeRankOne.isFinitePresentation (hM : LocallyFreeRankOne M) :
    M.IsFinitePresentation := by
  apply coherent_of_neighborhoods
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x
  exact ⟨U, hx, (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
    e.symm (unitSheaf_isFinitePresentation U.toScheme)⟩

/-- An actual section on a principal open has a global numerator. -/
theorem exists_principalSection_numerator [M.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] (r : Γ(X, ⊤))
    (U : X.Opens) (hU : U = X.basicOpen r) (s : Γ(M, U)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)), M.presheaf.map U.leTop.op t =
      (X.presheaf.map U.leTop.op r) ^ n • s := by
  have hρ : affineBaseScalars X.toSpecΓ = RingHom.id Γ(X, ⊤) := by
    simp [affineBaseScalars, Scheme.toSpecΓ_appTop]
  have h := sectionBaseRestriction_isLocalized X.toSpecΓ M r
  rw [hρ, X.toSpecΓ_preimage_basicOpen r, ← hU] at h
  let := h
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    (baseRestriction M (RingHom.id Γ(X, ⊤)) (show U ≤ ⊤ from le_top)) r s
  refine ⟨n, t, ?_⟩
  change X.presheaf.map U.leTop.op (r ^ n) • s = M.presheaf.map U.leTop.op t at ht
  simpa only [map_pow] using ht.symm

end FLT.Mazur.FCurve
