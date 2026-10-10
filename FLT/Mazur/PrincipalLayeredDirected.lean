/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLayeredStages

/-!
# Commuting refinements of two incidence layers

First refine the lower diagram, then detect equality of the upper arrows.
The middle relation sets remain shared throughout both operations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z v' w'

variable {R : Type u} [CommRing R]
  {ι : Type v} {κ : Type w} {τ : Type v'} {E : κ → Type z} {F : τ → Type w'}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {C : τ → Type u} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  [∀ k, Algebra.FiniteType R (C k)]
  {src : ∀ j, E j → ι} {mid : ∀ k, F k → κ}
  {a : ∀ i, A i} {b : ∀ j, B j} {c : ∀ k, C k}
  {f : ∀ j e, Localization.Away (a (src j e)) →ₐ[R] Localization.Away (b j)}
  {g : ∀ k e, Localization.Away (b (mid k e)) →ₐ[R] Localization.Away (c k)}
  [∀ j, Finite (E j)] [∀ k, Finite (F k)]

omit [∀ j, Finite (E j)] in
/-- Extend a layered diagram over a specified refinement of its lower layer. -/
theorem exists_principalLayeredStage_extension_over
    (x : PrincipalLayeredStage src mid a b c f g) (l : PrincipalBipartiteStage src a b f)
    (hl : x.lower ≤ l) (t : ∀ k, Finset (relationIdeal R (C k))) :
    ∃ y : PrincipalLayeredStage src mid a b c f g,
      x ≤ y ∧ y.lower = l ∧ t ≤ y.target := by
  classical
  obtain ⟨z, hz, ht⟩ := exists_principalBipartiteStage (src := mid) (a := b) (b := c)
    (f := g) l.target (fun k ↦ x.target k ∪ t k)
  have hs : (principalLayeredUpper x).source ≤ z.source := by
    rw [hz]
    exact principalBipartite_target_mono hl
  have hxt : (principalLayeredUpper x).target ≤ z.target :=
    fun k ↦ Finset.subset_union_left.trans (ht k)
  obtain ⟨w, hxw, hzw, hw⟩ := exists_principalBipartiteStage_compare
    (principalLayeredUpper x) z hs hxt
  let y := principalLayeredOfLayers l w (hw.trans hz)
  have hyL : y.lower = l := principalLayeredOfLayers_lower _ _ _
  have hyU : principalLayeredUpper y = w := principalLayeredOfLayers_upper _ _ _
  have hxy : x ≤ y := by
    constructor
    · rw [hyL]
      exact hl
    · rw [hyU]
      exact hxw
  refine ⟨y, hxy, hyL, ?_⟩
  change t ≤ (principalLayeredUpper y).target
  rw [hyU]
  exact fun k ↦ Finset.subset_union_right.trans
    ((ht k).trans (principalBipartite_target_mono hzw k))

/-- Extend a layered diagram past arbitrary relation bounds at all levels. -/
theorem exists_principalLayeredStage_extension (x : PrincipalLayeredStage src mid a b c f g)
    (s : ∀ i, Finset (relationIdeal R (A i))) (t : ∀ j, Finset (relationIdeal R (B j)))
    (q : ∀ k, Finset (relationIdeal R (C k))) :
    ∃ y : PrincipalLayeredStage src mid a b c f g,
      x ≤ y ∧ s ≤ y.lower.source ∧ t ≤ y.lower.target ∧ q ≤ y.target := by
  obtain ⟨l, hl, hs, ht⟩ := exists_principalBipartiteStage_extension x.lower s t
  obtain ⟨y, hxy, hy, hq⟩ := exists_principalLayeredStage_extension_over x l hl q
  refine ⟨y, hxy, ?_, ?_, hq⟩
  · rw [hy]
    exact hs
  · rw [hy]
    exact ht

omit [∀ j, Finite (E j)] in
/-- A common lower refinement can be extended to a common layered refinement. -/
theorem exists_principalLayeredStage_common_over
    (x y : PrincipalLayeredStage src mid a b c f g) (l : PrincipalBipartiteStage src a b f)
    (hx : x.lower ≤ l) (hy : y.lower ≤ l) :
    ∃ z : PrincipalLayeredStage src mid a b c f g, x ≤ z ∧ y ≤ z ∧ z.lower = l := by
  obtain ⟨z, hxz, hzL, hyT⟩ := exists_principalLayeredStage_extension_over x l hx y.target
  have hs : (principalLayeredUpper y).source ≤ (principalLayeredUpper z).source := by
    change y.lower.target ≤ z.lower.target
    rw [hzL]
    exact principalBipartite_target_mono hy
  obtain ⟨w, hyw, hzw, hw⟩ := exists_principalBipartiteStage_compare
    (principalLayeredUpper y) (principalLayeredUpper z) hs hyT
  let t := principalLayeredOfLayers z.lower w hw
  have htL : t.lower = z.lower := principalLayeredOfLayers_lower _ _ _
  have htU : principalLayeredUpper t = w := principalLayeredOfLayers_upper _ _ _
  have hzt : z ≤ t := by
    constructor
    · rw [htL]
    · rw [htU]
      exact hzw
  refine ⟨t, hxz.trans hzt, ?_, htL.trans hzL⟩
  constructor
  · rw [htL, hzL]
    exact hy
  · rw [htU]
    exact hyw

/-- The combined index has common commuting refinements. -/
instance principalLayeredStageDirected :
    IsDirectedOrder (PrincipalLayeredStage src mid a b c f g) where
  directed x y := by
    obtain ⟨l, hx, hy⟩ := exists_ge_ge x.lower y.lower
    obtain ⟨z, hxz, hyz, _⟩ := exists_principalLayeredStage_common_over x y l hx hy
    exact ⟨z, hxz, hyz⟩

/-- Two successive finite incidence layers form a filtered category. -/
instance principalLayeredStageFiltered :
    CategoryTheory.IsFiltered (PrincipalLayeredStage src mid a b c f g) := inferInstance

end FLT.Mazur.FiniteTypeRelationModel
