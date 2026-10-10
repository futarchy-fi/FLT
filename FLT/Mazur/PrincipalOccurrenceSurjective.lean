/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceDirected
public import FLT.Mazur.FiniteTypePrincipalSurjectiveLifts

/-!
# Surjective shared occurrence coordinates

All coordinate lifts become surjective while keeping every ambient chart
stage fixed. Incoming maps share one enlarged target relation set. Once
surjective, the coordinates remain surjective under any commuting refinement.
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
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}

/-- Enlarge every shared target, retaining the ambient source stages and all coordinates. -/
def principalOccurrenceTargetExtension (x : PrincipalOccurrenceStage dst a b f)
    (t : ∀ j, Finset (relationIdeal R (B j))) (ht : x.target ≤ t) :
    PrincipalOccurrenceStage dst a b f where
  source := x.source
  target := t
  hom i e := (principalTransition (b (dst i e)) (ht (dst i e))).comp (x.hom i e)
  fac i e := by rw [← AlgHom.comp_assoc, principalStageMap_transition, x.fac]

/-- Target extension is a refinement on each complete coordinate ring. -/
theorem principalOccurrenceTargetExtension_le (x : PrincipalOccurrenceStage dst a b f)
    (t : ∀ j, Finset (relationIdeal R (B j))) (ht : x.target ≤ t) :
    x ≤ principalOccurrenceTargetExtension x t ht := by
  refine ⟨le_rfl, ht, fun i e ↦ ?_⟩
  change ((principalTransition (b (dst i e)) (ht (dst i e))).comp (x.hom i e)).comp
    (principalTransition (a i e) (le_refl (x.source i))) = _
  rw [principalTransition_refl, AlgHom.comp_id]
  rfl

/-- Every commuting refinement preserves surjectivity of all coordinate maps. -/
theorem principalOccurrence_surjective_mono {x y : PrincipalOccurrenceStage dst a b f}
    (hxy : x ≤ y) (hx : ∀ i e, Function.Surjective (x.hom i e)) :
    ∀ i e, Function.Surjective (y.hom i e) := by
  intro i e
  have h := (FiniteRelationLocalization.transition_surjective R (relationIdeal R (B (dst i e)))
    (principalRepresentative R (B (dst i e)) (b (dst i e)))
    (principalOccurrence_target_mono hxy (dst i e))).comp (hx i e)
  change Function.Surjective
    ((principalTransition (b (dst i e)) (principalOccurrence_target_mono hxy (dst i e))).comp
      (x.hom i e)) at h
  rw [← principalOccurrence_hom_comm hxy i e] at h
  exact Function.Surjective.of_comp h

variable [Finite ι] [∀ i, Finite (J i)]

/-- Original surjections become surjective simultaneously at shared overlap targets. -/
theorem exists_principalOccurrence_surjective (hf : ∀ i e, Function.Surjective (f i e))
    (x : PrincipalOccurrenceStage dst a b f) :
    ∃ y : PrincipalOccurrenceStage dst a b f, x ≤ y ∧ y.source = x.source ∧
      ∀ i e, Function.Surjective (y.hom i e) := by
  classical
  let _ (j : κ) : Fintype (PrincipalIncoming (dst := dst) j) := Fintype.ofFinite _
  have hx (j) (e : PrincipalIncoming (dst := dst) j) :
      Function.Surjective ((principalStageMap R (B j) (b j) (x.target j)).comp
        (principalOccurrenceIncomingHom x j e)) := by
    obtain ⟨⟨i, k⟩, rfl⟩ := e
    change Function.Surjective ((principalStageMap R _ _ _).comp (x.hom i k))
    rw [x.fac]
    exact (hf i k).comp (principalStageMap_surjective R (A i) (a i k) (x.source i))
  choose t ht hs using fun j e ↦ exists_principal_surjective_stage (b j) (x.target j)
    (principalOccurrenceIncomingHom x j e) (hx j e)
  let q (j) := x.target j ∪ Finset.univ.biUnion (t j)
  have hq : x.target ≤ q := fun _ ↦ Finset.subset_union_left
  have htq (j) (e : PrincipalIncoming (dst := dst) j) : t j e ≤ q j := by
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, hz⟩)
  refine ⟨principalOccurrenceTargetExtension x q hq,
    principalOccurrenceTargetExtension_le x q hq, rfl, fun i e ↦ ?_⟩
  let k : PrincipalIncoming (dst := dst) (dst i e) := ⟨⟨i, e⟩, rfl⟩
  have h := (FiniteRelationLocalization.transition_surjective R (relationIdeal R (B (dst i e)))
    (principalRepresentative R (B (dst i e)) (b (dst i e)))
    (htq (dst i e) k)).comp (hs (dst i e) k)
  change Function.Surjective ((principalTransition (b (dst i e)) (htq (dst i e) k)).comp
    ((principalTransition (b (dst i e)) (ht (dst i e) k)).comp (x.hom i e))) at h
  rw [← AlgHom.comp_assoc, principalTransition_comp] at h
  exact h

end FLT.Mazur.FiniteTypeRelationModel
