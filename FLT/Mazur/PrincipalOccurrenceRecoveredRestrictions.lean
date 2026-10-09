/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceFiniteRestrictions
public import FLT.Mazur.PrincipalFanOriginalRecovery

/-!
# Finite restrictions with proved original recovery

Starting with surjective finite coordinates, construct shared later overlap
stages and actual finite restrictions. Retain both the ambient path equations
and the original recovery squares, proved by rigidity of the old coordinates.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [Finite ι] [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))

/-- Construct finite restrictions and prove their original recovery simultaneously. -/
theorem exists_principalOccurrence_recovered_restrictions
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
    (hx : ∀ i k, Function.Surjective (x.hom i k))
    (s : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ (t : ∀ j, Finset (relationIdeal R (B j))) (ht : x.target ≤ t), s ≤ t ∧
      let y := principalOccurrenceTargetExtension x t ht
      ∃ ρ : ∀ i k l,
        PrincipalStage R (B (dst i k)) (b (dst i k)) (x.target (dst i k)) →ₐ[R]
          PrincipalFanRestrictionTarget (principalOccurrenceFan y i) k l,
        (∀ i k l, (ρ i k l).comp (principalFanAmbient (principalOccurrenceFan x i) k) =
          (principalFanRestrictionInclusion (principalOccurrenceFan y i) k l).comp
            (principalFanAmbient (principalOccurrenceFan y i) l)) ∧
        ∀ i k l,
          (principalFanRestrictionProjection (e i) (principalOccurrenceFan y i) k l).comp
            (ρ i k l) =
          (principalFanOriginalRestriction (e i) (principalOccurrenceFan y i) k l).comp
            (principalStageMap R (B (dst i k)) (b (dst i k)) (x.target (dst i k))) := by
  obtain ⟨t, ht, hst, ρ, hρ⟩ := exists_principalOccurrence_finite_restrictions e x s
  let y := principalOccurrenceTargetExtension x t ht
  have hxy : x ≤ y := principalOccurrenceTargetExtension_le x t ht
  refine ⟨t, ht, hst, ρ, hρ, fun i k l ↦ ?_⟩
  apply principalFanRestriction_original_recovery (e i) (principalOccurrenceFan_mono hxy i)
    k l (hx i k) (ρ i k l)
  exact hρ i k l

end FLT.Mazur.FiniteTypeRelationModel
