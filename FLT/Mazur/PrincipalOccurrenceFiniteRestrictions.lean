/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanFiniteRestrictions
public import FLT.Mazur.PrincipalFanRestrictionUniqueness
public import FLT.Mazur.PrincipalOccurrenceSurjective
public import FLT.Mazur.PrincipalOccurrenceTargetBounds

/-!
# Shared finite target restrictions from original geometry

All outgoing fans share a single new relation set at each overlap target.
The finite restrictions start at the old overlap stages and land in the exact
localized targets of the refined occurrence model. Every old coordinate square
and every ambient restriction equation is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


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

/-- Construct all finite restrictions into shared refined targets with old source stages. -/
theorem exists_principalOccurrence_finite_restrictions
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
    (s : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ (t : ∀ j, Finset (relationIdeal R (B j))) (ht : x.target ≤ t), s ≤ t ∧
      let y := principalOccurrenceTargetExtension x t ht
      ∃ ρ : ∀ i k l,
        PrincipalStage R (B (dst i k)) (b (dst i k)) (x.target (dst i k)) →ₐ[R]
          PrincipalFanRestrictionTarget (principalOccurrenceFan y i) k l,
        ∀ i k l, (ρ i k l).comp (principalFanAmbient (principalOccurrenceFan x i) k) =
          (principalFanRestrictionInclusion (principalOccurrenceFan y i) k l).comp
              (principalFanAmbient (principalOccurrenceFan y i) l) := by
  choose q hq ρ hρ using fun i l ↦ exists_principalFan_finite_restrictions
    (e i) (principalOccurrenceFan x i) l ⟨x.target (dst i l), by
      change x.target (dst i l) ≤ x.target (dst i l)
      exact le_rfl⟩
  classical
  obtain ⟨t, ht, hqt⟩ := exists_principalOccurrence_target_bounds
    (fun i l ↦ (q i l).val) (fun j ↦ x.target j ∪ s j)
  have hxt : x.target ≤ t := fun j ↦ Finset.subset_union_left.trans (ht j)
  have hst : s ≤ t := fun j ↦ Finset.subset_union_right.trans (ht j)
  let y := principalOccurrenceTargetExtension x t hxt
  let k (i) (l : J i) : Set.Ici (x.target (dst i l)) := ⟨t (dst i l), hxt (dst i l)⟩
  let τ (i) (j l : J i) := FiniteRelationIterated.transition R
    (relationIdeal R (B (dst i l))) (principalRepresentative R (B (dst i l)) (b (dst i l)))
    (x.target (dst i l)) (principalFanRestrictionDenominator (principalOccurrenceFan x i) j l)
    (show q i l ≤ k i l from hqt i l)
  refine ⟨t, hxt, hst, fun i j l ↦ (τ i j l).comp (ρ i l j), fun i j l ↦ ?_⟩
  change ((τ i j l).comp (ρ i l j)).comp
    (principalFanAmbient (principalOccurrenceFan x i) j) = _
  rw [AlgHom.comp_assoc, hρ]
  apply AlgHom.ext
  intro z
  change τ i j l (algebraMap _ _
    (principalTransition (b (dst i l)) (q i l).property
      (principalFanAmbient (principalOccurrenceFan x i) l z))) =
    algebraMap _ _ (principalTransition (b (dst i l)) (hxt (dst i l))
      (principalFanAmbient (principalOccurrenceFan x i) l z))
  dsimp only [τ]
  rw [FiniteRelationIterated.transition_algebraMap]
  congr 1
  exact AlgHom.congr_fun (principalTransition_comp (b (dst i l))
    (q i l).property (hqt i l)) (principalFanAmbient (principalOccurrenceFan x i) l z)

end FLT.Mazur.FiniteTypeRelationModel
