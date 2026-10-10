/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalBipartiteStages

/-!
# Common refinements of chart and overlap incidence diagrams

Each overlap has finitely many incoming arrows. Detecting equality at every
target constructs common refinements without changing the shared sources.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {E : κ → Type z}
  [∀ j, Finite (E j)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {src : ∀ j, E j → ι} {a : ∀ i, A i} {b : ∀ j, B j}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}

/-- Impose every old refinement square by enlarging all target relation sets. -/
theorem exists_principalBipartiteStage_compare (x z : PrincipalBipartiteStage src a b f)
    (hs : x.source ≤ z.source) (ht : x.target ≤ z.target) :
    ∃ w : PrincipalBipartiteStage src a b f, x ≤ w ∧ z ≤ w ∧ w.source = z.source := by
  have he (j) (e : E j) : (principalStageMap R (B j) (b j) (z.target j)).comp
        ((z.hom j e).comp (principalTransition (a (src j e)) (hs (src j e)))) =
      (principalStageMap R (B j) (b j) (z.target j)).comp
        ((principalTransition (b j) (ht j)).comp (x.hom j e)) := by
    rw [← AlgHom.comp_assoc, z.fac, AlgHom.comp_assoc, principalStageMap_transition,
      ← AlgHom.comp_assoc, principalStageMap_transition, x.fac]
  choose q hq hcomm using fun j ↦ exists_principal_hom_eq_finite (b j)
    (fun e ↦ PrincipalStage R (A (src j e)) (a (src j e)) (x.source (src j e)))
    (z.target j)
    (fun e ↦ (z.hom j e).comp (principalTransition (a (src j e)) (hs (src j e))))
    (fun e ↦ (principalTransition (b j) (ht j)).comp (x.hom j e)) (he j)
  let w : PrincipalBipartiteStage src a b f :=
    { source := z.source
      target := q
      hom := fun j e ↦ (principalTransition (b j) (hq j)).comp (z.hom j e)
      fac := fun j e ↦ by
        rw [← AlgHom.comp_assoc, principalStageMap_transition, z.fac] }
  refine ⟨w, ⟨hs, fun j ↦ ⟨fun e ↦ hs (src j e), (ht j).trans (hq j), ?_⟩⟩,
    ⟨le_rfl, fun j ↦ ⟨le_rfl, hq j, ?_⟩⟩, rfl⟩
  · intro e
    change ((principalTransition (b j) (hq j)).comp (z.hom j e)).comp
        (principalTransition (a (src j e)) (hs (src j e))) = _
    rw [AlgHom.comp_assoc, hcomm, ← AlgHom.comp_assoc, principalTransition_comp]
    rfl
  · intro e
    change ((principalTransition (b j) (hq j)).comp (z.hom j e)).comp
        (principalTransition (a (src j e)) (le_refl (z.source (src j e)))) = _
    rw [principalTransition_refl, AlgHom.comp_id]
    rfl

/-- A whole incidence diagram extends past arbitrary chart and overlap bounds. -/
theorem exists_principalBipartiteStage_extension (x : PrincipalBipartiteStage src a b f)
    (s : ∀ i, Finset (relationIdeal R (A i))) (t : ∀ j, Finset (relationIdeal R (B j))) :
    ∃ w : PrincipalBipartiteStage src a b f, x ≤ w ∧ s ≤ w.source ∧ t ≤ w.target := by
  classical
  obtain ⟨z, hzS, hzT⟩ := exists_principalBipartiteStage (src := src) (a := a) (b := b)
    (f := f) (fun i ↦ x.source i ∪ s i) (fun j ↦ x.target j ∪ t j)
  have hxs : x.source ≤ z.source := by
    rw [hzS]
    exact fun _ ↦ Finset.subset_union_left
  have hxt : x.target ≤ z.target := fun j ↦ Finset.subset_union_left.trans (hzT j)
  obtain ⟨w, hxw, hzw, hw⟩ := exists_principalBipartiteStage_compare x z hxs hxt
  refine ⟨w, hxw, ?_, fun j ↦ ?_⟩
  · rw [hw, hzS]
    exact fun _ ↦ Finset.subset_union_right
  · exact Finset.subset_union_right.trans
      ((hzT j).trans (principalBipartite_target_mono hzw j))

/-- Shared source charts do not obstruct common commuting refinements. -/
instance principalBipartiteStageDirected :
    IsDirectedOrder (PrincipalBipartiteStage src a b f) where
  directed x y := by
    obtain ⟨z, hxz, hyS, hyT⟩ := exists_principalBipartiteStage_extension x y.source y.target
    obtain ⟨w, hyw, hzw, _⟩ := exists_principalBipartiteStage_compare y z hyS hyT
    exact ⟨w, hxz.trans hzw, hyw⟩

/-- Incidence diagrams with shared chart stages form a filtered category. -/
instance principalBipartiteStageFiltered :
    CategoryTheory.IsFiltered (PrincipalBipartiteStage src a b f) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
