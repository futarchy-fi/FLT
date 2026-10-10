/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceExistence

/-!
# Directed refinement with shared incoming and outgoing occurrences

Finite equality detection at each shared target imposes every coordinate
square. The ambient source stages remain shared, with different principal
denominators allowed at each occurrence.
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

/-- The current coordinate map, indexed by its incoming target fiber. -/
def principalOccurrenceIncomingHom (x : PrincipalOccurrenceStage dst a b f)
    (j : κ) (e : PrincipalIncoming (dst := dst) j) :
    PrincipalStage R (A e.val.1) (a e.val.1 e.val.2) (x.source e.val.1) →ₐ[R]
      PrincipalStage R (B j) (b j) (x.target j) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  exact x.hom i k

/-- Reindexing a finite-stage coordinate retains its original factorization. -/
theorem principalOccurrenceIncomingHom_fac (x : PrincipalOccurrenceStage dst a b f)
    (j : κ) (e : PrincipalIncoming (dst := dst) j) :
    (principalStageMap R (B j) (b j) (x.target j)).comp
      (principalOccurrenceIncomingHom x j e) =
    (principalIncomingMap f j e).comp
      (principalStageMap R (A e.val.1) (a e.val.1 e.val.2) (x.source e.val.1)) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := e
  exact x.fac i k

variable [Finite ι] [∀ i, Finite (J i)]

/-- Impose all old squares by enlarging shared targets, retaining the chosen sources exactly. -/
theorem exists_principalOccurrenceStage_compare (x y : PrincipalOccurrenceStage dst a b f)
    (hs : x.source ≤ y.source) (ht : x.target ≤ y.target) :
    ∃ z : PrincipalOccurrenceStage dst a b f, x ≤ z ∧ y ≤ z ∧ z.source = y.source := by
  have he (j) (e : PrincipalIncoming (dst := dst) j) :
      (principalStageMap R (B j) (b j) (y.target j)).comp
        ((principalOccurrenceIncomingHom y j e).comp
          (principalTransition (a e.val.1 e.val.2) (hs e.val.1))) =
      (principalStageMap R (B j) (b j) (y.target j)).comp
        ((principalTransition (b j) (ht j)).comp (principalOccurrenceIncomingHom x j e)) := by
    rw [← AlgHom.comp_assoc, principalOccurrenceIncomingHom_fac, AlgHom.comp_assoc,
      principalStageMap_transition, ← AlgHom.comp_assoc, principalStageMap_transition,
      principalOccurrenceIncomingHom_fac]
  choose q hq hc using fun j ↦ exists_principal_hom_eq_finite (b j)
    (fun e : PrincipalIncoming (dst := dst) j ↦
      PrincipalStage R (A e.val.1) (a e.val.1 e.val.2) (x.source e.val.1))
    (y.target j)
    (fun e ↦ (principalOccurrenceIncomingHom y j e).comp
      (principalTransition (a e.val.1 e.val.2) (hs e.val.1)))
    (fun e ↦ (principalTransition (b j) (ht j)).comp
      (principalOccurrenceIncomingHom x j e)) (he j)
  let z : PrincipalOccurrenceStage dst a b f :=
    { source := y.source
      target := q
      hom i e := (principalTransition (b (dst i e)) (hq (dst i e))).comp (y.hom i e)
      fac i e := by rw [← AlgHom.comp_assoc, principalStageMap_transition, y.fac] }
  refine ⟨z, ⟨hs, ht.trans hq, fun i e ↦ ?_⟩,
    ⟨le_rfl, hq, fun i e ↦ ?_⟩, rfl⟩
  · have h := hc (dst i e) ⟨⟨i, e⟩, rfl⟩
    change (principalTransition (b (dst i e)) (hq (dst i e))).comp
      ((y.hom i e).comp (principalTransition (a i e) (hs i))) =
      (principalTransition (b (dst i e)) (hq (dst i e))).comp
        ((principalTransition (b (dst i e)) (ht (dst i e))).comp (x.hom i e)) at h
    change ((principalTransition (b (dst i e)) (hq (dst i e))).comp (y.hom i e)).comp
      (principalTransition (a i e) (hs i)) = _
    rw [AlgHom.comp_assoc, h, ← AlgHom.comp_assoc, principalTransition_comp]
  · change ((principalTransition (b (dst i e)) (hq (dst i e))).comp (y.hom i e)).comp
      (principalTransition (a i e) (le_refl (y.source i))) = _
    rw [principalTransition_refl, AlgHom.comp_id]

/-- Arbitrary chart and overlap bounds have a commuting occurrence refinement. -/
theorem exists_principalOccurrenceStage_extension (x : PrincipalOccurrenceStage dst a b f)
    (s : ∀ i, Finset (relationIdeal R (A i))) (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ z : PrincipalOccurrenceStage dst a b f, x ≤ z ∧ s ≤ z.source ∧ t ≤ z.target := by
  classical
  obtain ⟨y, hyS, hyT⟩ := exists_principalOccurrenceStage f
    (fun i ↦ x.source i ∪ s i) (fun j ↦ x.target j ∪ t j)
  have hs : x.source ≤ y.source := by
    rw [hyS]
    exact fun _ ↦ Finset.subset_union_left
  obtain ⟨z, hxz, hyz, hz⟩ := exists_principalOccurrenceStage_compare x y hs
    (fun j ↦ Finset.subset_union_left.trans (hyT j))
  refine ⟨z, hxz, ?_, fun j ↦ Finset.subset_union_right.trans
    ((hyT j).trans (principalOccurrence_target_mono hyz j))⟩
  rw [hz, hyS]
  exact fun _ ↦ Finset.subset_union_right

/-- The full shared occurrence index is directed. -/
instance principalOccurrenceStageDirected :
    IsDirectedOrder (PrincipalOccurrenceStage dst a b f) where
  directed x y := by
    obtain ⟨z, hxz, hyS, hyT⟩ := exists_principalOccurrenceStage_extension x y.source y.target
    obtain ⟨q, hyq, hzq, _⟩ := exists_principalOccurrenceStage_compare y z hyS hyT
    exact ⟨q, hxz.trans hzq, hyq⟩

/-- Shared targets and different occurrence denominators give a filtered model category. -/
instance principalOccurrenceStageFiltered :
    CategoryTheory.IsFiltered (PrincipalOccurrenceStage dst a b f) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
