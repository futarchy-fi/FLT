/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramCoordinates

/-!
# Recover occurrence stages from combined diagram coordinates

A shared polynomial stage and its actual quotient recovery squares define
an occurrence stage. Commuting old diagram squares prove refinement, so
surjective occurrence coordinates are retained under the combined construction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationLocalization.toQuotient

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e)))


variable (s : ∀ i, Finset (relationIdeal R (A i)))
  (t : ∀ j, Finset (relationIdeal R (B j)))
  (F : ∀ i k, PrincipalStage R (A i) (a i k) (s i) →ₐ[R]
    PrincipalStage R (B (dst i k)) (b (dst i k)) (t (dst i k)))
  (hF : ∀ i k,
    (FiniteRelationLocalization.toQuotient R (relationIdeal R (B (dst i k)))
      (principalRepresentative R (B (dst i k)) (b (dst i k))) (t (dst i k))).comp (F i k) =
    (principalQuotientEquiv R (B (dst i k)) (b (dst i k))).symm.toAlgHom.comp
      ((f i k).comp (principalStageMap R (A i) (a i k) (s i))))

/-- Quotient recovery squares define actual occurrence stages at the specified shared bounds. -/
def principalOccurrenceStageOfDiagram : PrincipalOccurrenceStage dst a b f where
  source := s
  target := t
  hom := F
  fac i k := by
    apply AlgHom.ext
    intro z
    have h := AlgHom.congr_fun (hF i k) z
    have h' := congrArg (principalQuotientEquiv R (B (dst i k)) (b (dst i k))) h
    change principalStageMap R (B (dst i k)) (b (dst i k)) (t (dst i k)) (F i k z) =
      principalQuotientEquiv R (B (dst i k)) (b (dst i k))
        ((principalQuotientEquiv R (B (dst i k)) (b (dst i k))).symm
          (f i k (principalStageMap R (A i) (a i k) (s i) z))) at h'
    rw [AlgEquiv.apply_symm_apply] at h'
    exact h'

/-- Commuting old coordinate squares give the full occurrence refinement relation. -/
theorem principalOccurrenceStageOfDiagram_le (x : PrincipalOccurrenceStage dst a b f)
    (hs : x.source ≤ s) (ht : x.target ≤ t)
    (hOld : ∀ i k, (F i k).comp (principalTransition (a i k) (hs i)) =
      (principalTransition (b (dst i k)) (ht (dst i k))).comp (x.hom i k)) :
    x ≤ principalOccurrenceStageOfDiagram f s t F hF :=
  ⟨hs, ht, hOld⟩

end FLT.Mazur.FiniteTypeRelationModel
