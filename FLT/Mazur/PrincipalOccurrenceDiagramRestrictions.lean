/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramCoordinates
public import FLT.Mazur.PrincipalFanOriginalRecovery

/-!
# Actual double-open denominators on the combined diagram

Every denominator is the image of the other source open under the target
coordinate. The original restriction maps use the given chart isomorphisms,
so the diagram edges contain no assumed extension or recovery data.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

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

/-- Literal double-open denominators at the shared old target stages. -/
def principalOccurrenceDiagramDenominator :
    ∀ j o, PrincipalOccurrenceDoubleLabel dst j o →
      FiniteRelationLocalization.Stage (I j) (r j o) (s j) := by
  intro j o p
  cases j with
  | inl _ => exact p.elim
  | inr j =>
    obtain ⟨⟨i, k, l⟩, rfl⟩ := p
    exact principalFanRestrictionDenominator (principalOccurrenceFan x i) k l

/-- Original restriction arrows in the combined quotient diagram. -/
def principalOccurrenceDiagramRestriction :
    ∀ i j o p (h : PrincipalOccurrenceRestrictionEdge dst i j o p),
    FiniteRelationLocalization.Quotient (I i)
        (r i (principalOccurrenceRestrictionSource dst i j o p h)) →ₐ[R]
      FiniteRelationIterated.Quotient R (I j) (r j o) (s j)
        (principalOccurrenceDiagramDenominator e x j o p) := by
  intro i j o p h
  cases j with
  | inl _ => exact p.elim
  | inr j =>
    cases i with
    | inl _ => exact h.elim
    | inr i =>
      obtain ⟨⟨k, l, m⟩, rfl⟩ := p
      obtain ⟨rfl⟩ := h
      exact (principalFanOriginalRestriction (e k) (principalOccurrenceFan x k) l m).comp
        (principalQuotientEquiv R (B (dst k l)) (b (dst k l))).toAlgHom

end FLT.Mazur.FiniteTypeRelationModel
