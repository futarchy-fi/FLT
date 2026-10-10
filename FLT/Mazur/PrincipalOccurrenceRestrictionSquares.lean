/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDiagramFiniteRestrictions
public import FLT.Mazur.PrincipalOccurrenceStageFromDiagram
public import FLT.Mazur.PrincipalOccurrenceRefinedPaths

/-!
# Geometric refinement square predicates

Record the old and original squares for literal restrictions at a refined
occurrence stage, keeping earlier overlap sources explicit.
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



variable (t : ∀ j, Finset (relationIdeal R (B j)))
  (ρ : ∀ i k l, PrincipalStage R (B (dst i k)) (b (dst i k)) (t (dst i k)) →ₐ[R]
    PrincipalFanRestrictionTarget (principalOccurrenceFan x i) k l)




/-- Old restriction squares compare the actual earlier overlap sources. -/
def PrincipalOccurrenceRestrictionOldSquares (ht : t ≤ x.target)
    {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)} (hxy : x ≤ y)
    (σ : ∀ i k l,
      PrincipalStage R (B (dst i k)) (b (dst i k)) (y.target (dst i k)) →ₐ[R]
        PrincipalFanOldRestrictionTarget (principalOccurrenceFan_mono hxy i) k l) : Prop :=
  ∀ i k l, (σ i k l).comp (principalTransition (b (dst i k))
          ((ht (dst i k)).trans (principalOccurrence_target_mono hxy (dst i k)))) =
          (FiniteRelationIterated.transition R (relationIdeal R (B (dst i l)))
            (principalRepresentative R (B (dst i l)) (b (dst i l))) (x.target (dst i l))
            (principalFanRestrictionDenominator (principalOccurrenceFan x i) k l)
            (show (⟨x.target (dst i l), le_refl (x.target (dst i l))⟩ :
              Set.Ici (x.target (dst i l))) ≤
              ⟨y.target (dst i l), principalOccurrence_target_mono hxy (dst i l)⟩ from
                principalOccurrence_target_mono hxy (dst i l))).comp
            ((principalFanInitialRestrictionEquiv (e i)
              (principalOccurrenceFan x i) k l).toAlgHom.comp (ρ i k l))

/-- Refined restrictions recover the prescribed original double-open maps. -/
def PrincipalOccurrenceRestrictionRecovery
    {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)} (hxy : x ≤ y)
    (σ : ∀ i k l,
      PrincipalStage R (B (dst i k)) (b (dst i k)) (y.target (dst i k)) →ₐ[R]
        PrincipalFanOldRestrictionTarget (principalOccurrenceFan_mono hxy i) k l) : Prop :=
  ∀ i k l, (FiniteRelationIterated.toQuotient R (relationIdeal R (B (dst i l)))
          (principalRepresentative R (B (dst i l)) (b (dst i l))) (x.target (dst i l))
          (principalFanRestrictionDenominator (principalOccurrenceFan x i) k l)
          ⟨y.target (dst i l), principalOccurrence_target_mono hxy (dst i l)⟩).comp
            (σ i k l) =
          (principalFanOriginalRestriction (e i) (principalOccurrenceFan x i) k l).comp
            (principalStageMap R (B (dst i k)) (b (dst i k)) (y.target (dst i k)))


end FLT.Mazur.FiniteTypeRelationModel
