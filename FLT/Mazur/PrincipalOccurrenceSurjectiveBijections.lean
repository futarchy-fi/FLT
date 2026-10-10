/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceRecoveredRestrictions
public import FLT.Mazur.PrincipalOccurrenceDiagramRefinement
public import FLT.Mazur.PrincipalOccurrenceMixedBijections

/-!
# Cofinal bijections from surjective occurrence coordinates

Finite restrictions and simultaneous diagram refinement supply the full
ambient paths needed for kernel patching. All target labels remain shared.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalFanInitialRestrictionEquiv
  principalFanOriginalRestriction principalQuotientEquiv principalFanRestrictionProjection
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

variable [Finite κ]

/-- Surjective occurrence coordinates refine cofinally to simultaneous bijections. -/
theorem exists_principalOccurrence_bijective_of_surjective
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
    (hx : ∀ i k, Function.Surjective (x.hom i k))
    (bs : ∀ i, Finset (relationIdeal R (A i)))
    (bt : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ w : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      x ≤ w ∧ bs ≤ w.source ∧ bt ≤ w.target ∧
        ∀ i k, Function.Bijective (w.hom i k) := by
  obtain ⟨t, ht, _hbt, ρ, hρ, hrec⟩ :=
    exists_principalOccurrence_recovered_restrictions e x hx bt
  let y := principalOccurrenceTargetExtension x t ht
  have hxy : x ≤ y := principalOccurrenceTargetExtension_le x t ht
  obtain ⟨w, hyw, hs, hb, hw⟩ :=
    exists_principalOccurrence_bijective_of_mixed_restrictions e hxy hx ρ hρ hrec bs bt
  exact ⟨w, hxy.trans hyw, hs, hb, hw⟩

end FLT.Mazur.FiniteTypeRelationModel
