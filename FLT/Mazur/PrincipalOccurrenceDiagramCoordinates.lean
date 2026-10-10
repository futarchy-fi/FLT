/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramEdges

/-!
# Coordinate arrows in the combined polynomial diagram

The maps here are the actual original and finite occurrence coordinates.
Conjugating by the principal presentation equivalences gives the exact
quotient recovery square required by simultaneous occurrence refinement.
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
  (f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e)))

local notation "C" => PrincipalOccurrenceAmbient A B
local notation "I" => fun i ↦ relationIdeal R (C i)
local notation "r" => principalOccurrenceAmbientRepresentative A B a b

/-- Actual original coordinate arrows in canonical polynomial quotient coordinates. -/
def principalOccurrenceDiagramCoordinate :
    ∀ i j o (e : PrincipalOccurrenceCoordinateEdge dst i j o),
    FiniteRelationLocalization.Quotient (I i)
        (r i (principalOccurrenceCoordinateSource dst i j o e)) →ₐ[R]
      FiniteRelationLocalization.Quotient (I j) (r j o) := by
  intro i j o e
  cases i with
  | inr _ => cases j <;> exact e.elim
  | inl i =>
    cases j with
    | inl _ => exact e.elim
    | inr j =>
      obtain ⟨k, rfl⟩ := e
      exact (principalQuotientEquiv R (B (dst i k)) (b (dst i k))).symm.toAlgHom.comp
        ((f i k).comp (principalQuotientEquiv R (A i) (a i k)).toAlgHom)

variable (x : PrincipalOccurrenceStage dst a b f)

local notation "s" => principalOccurrenceAmbientRelations A B x.source x.target

/-- The finite arrows use exactly the old source and shared target stages. -/
def principalOccurrenceDiagramFiniteCoordinate :
    ∀ i j o (e : PrincipalOccurrenceCoordinateEdge dst i j o),
    FiniteRelationLocalization.Stage (I i)
        (r i (principalOccurrenceCoordinateSource dst i j o e)) (s i) →ₐ[R]
      FiniteRelationLocalization.Stage (I j) (r j o) (s j) := by
  intro i j o e
  cases i with
  | inr _ => cases j <;> exact e.elim
  | inl i =>
    cases j with
    | inl _ => exact e.elim
    | inr j =>
      obtain ⟨k, rfl⟩ := e
      exact x.hom i k

/-- Coordinate recovery in the canonical quotients follows from the existing stage square. -/
theorem principalOccurrenceDiagramCoordinate_recovery
    (i j : ι ⊕ κ) (o : PrincipalOccurrenceOpen (J := J) j)
    (e : PrincipalOccurrenceCoordinateEdge dst i j o) :
    (FiniteRelationLocalization.toQuotient R (I j) (r j o) (s j)).comp
      (principalOccurrenceDiagramFiniteCoordinate f x i j o e) =
    (principalOccurrenceDiagramCoordinate f i j o e).comp
      (FiniteRelationLocalization.toQuotient R (I i)
        (r i (principalOccurrenceCoordinateSource dst i j o e)) (s i)) := by
  cases i with
  | inr _ => cases j <;> exact e.elim
  | inl i =>
    cases j with
    | inl _ => exact e.elim
    | inr j =>
      obtain ⟨k, rfl⟩ := e
      apply AlgHom.ext
      intro z
      apply (principalQuotientEquiv R (B (dst i k)) (b (dst i k))).injective
      change principalStageMap R (B (dst i k)) (b (dst i k)) (x.target (dst i k))
          (x.hom i k z) =
        principalQuotientEquiv R (B (dst i k)) (b (dst i k))
          ((principalQuotientEquiv R (B (dst i k)) (b (dst i k))).symm
          (f i k (principalStageMap R (A i) (a i k) (x.source i) z)))
      rw [AlgEquiv.apply_symm_apply]
      exact AlgHom.congr_fun (x.fac i k) z

end FLT.Mazur.FiniteTypeRelationModel
