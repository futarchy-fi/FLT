/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramRestrictions
public import FLT.Mazur.PrincipalFanInitialRestriction

/-!
# Finite restriction arrows with independently staged sources

Package actual finite restrictions in the occurrence diagram. Source overlap
relations can precede the common target stage. The literal initial target
comparison transfers the original recovery square without changing its maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalFanInitialRestrictionEquiv
  principalFanOriginalRestriction principalQuotientEquiv principalFanRestrictionProjection
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))

local notation "C" => PrincipalOccurrenceAmbient A B
local notation "I" => fun i ↦ relationIdeal R (C i)
local notation "r" => principalOccurrenceAmbientRepresentative A B a b
local notation "s" => principalOccurrenceAmbientRelations A B x.source x.target


variable (t : ∀ j, Finset (relationIdeal R (B j)))
  (ρ : ∀ i k l, PrincipalStage R (B (dst i k)) (b (dst i k)) (t (dst i k)) →ₐ[R]
    PrincipalFanRestrictionTarget (principalOccurrenceFan x i) k l)

local notation "c" => principalOccurrenceAmbientRelations A B x.source t

/-- Retain old source overlap rings and convert only the double-open target. -/
def principalOccurrenceDiagramFiniteRestriction :
    ∀ i j o p (h : PrincipalOccurrenceRestrictionEdge dst i j o p),
    FiniteRelationLocalization.Stage (I i)
        (r i (principalOccurrenceRestrictionSource dst i j o p h)) (c i) →ₐ[R]
      FiniteRelationIterated.Stage R (I j) (r j o) (s j)
        (principalOccurrenceDiagramDenominator e x j o p) ⟨s j, le_refl (s j)⟩ := by
  intro i j o p h
  cases j with
  | inl _ => exact p.elim
  | inr j =>
    cases i with
    | inl _ => exact h.elim
    | inr i =>
      obtain ⟨⟨k, l, m⟩, rfl⟩ := p
      obtain ⟨rfl⟩ := h
      exact (principalFanInitialRestrictionEquiv
        (e k) (principalOccurrenceFan x k) l m).toAlgHom.comp
        (ρ k l m)

/-- Transfer the proved recovery square to precisely the mixed-source refinement API. -/
theorem principalOccurrenceDiagramFiniteRestriction_recovery
    (hρ : ∀ i k l,
      (principalFanRestrictionProjection (e i) (principalOccurrenceFan x i) k l).comp (ρ i k l) =
      (principalFanOriginalRestriction (e i) (principalOccurrenceFan x i) k l).comp
        (principalStageMap R (B (dst i k)) (b (dst i k)) (t (dst i k))))
    (i j : ι ⊕ κ) (o : PrincipalOccurrenceOpen (J := J) j)
    (p : PrincipalOccurrenceDoubleLabel dst j o)
    (h : PrincipalOccurrenceRestrictionEdge dst i j o p) :
    (FiniteRelationIterated.toQuotient R (I j) (r j o) (s j)
      (principalOccurrenceDiagramDenominator e x j o p) ⟨s j, le_refl (s j)⟩).comp
        (principalOccurrenceDiagramFiniteRestriction e x t ρ i j o p h) =
      (principalOccurrenceDiagramRestriction e x i j o p h).comp
        (FiniteRelationLocalization.toQuotient R (I i)
          (r i (principalOccurrenceRestrictionSource dst i j o p h)) (c i)) := by
  cases j with
  | inl _ => exact p.elim
  | inr j =>
    cases i with
    | inl _ => exact h.elim
    | inr i =>
      obtain ⟨⟨k, l, m⟩, rfl⟩ := p
      obtain ⟨rfl⟩ := h
      change (FiniteRelationIterated.toQuotient R (relationIdeal R (B (dst k m)))
        (principalRepresentative R (B (dst k m)) (b (dst k m))) (x.target (dst k m))
        (principalFanRestrictionDenominator (principalOccurrenceFan x k) l m)
        ⟨x.target (dst k m), le_refl (x.target (dst k m))⟩).comp
          ((principalFanInitialRestrictionEquiv (e k)
            (principalOccurrenceFan x k) l m).toAlgHom.comp (ρ k l m)) =
        (principalFanOriginalRestriction (e k) (principalOccurrenceFan x k) l m).comp
          (principalStageMap R (B (dst k l)) (b (dst k l)) (t (dst k l)))
      apply AlgHom.ext
      intro z
      have hp := AlgHom.congr_fun
        (principalFanInitialRestrictionEquiv_projection (e k)
          (principalOccurrenceFan x k) l m) (ρ k l m z)
      have hr := AlgHom.congr_fun (hρ k l m) z
      exact hp.trans hr

end FLT.Mazur.FiniteTypeRelationModel
