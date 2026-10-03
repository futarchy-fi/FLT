/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeIncidence
public import FLT.Mazur.PolygonNodeLocus
public import FLT.Mazur.ProjectiveLineEndpointCover

/-!
# Normalization over the polygon Laurent opens

The endpoint cover and nonsmoothness of nodes exclude extra preimages of the
Laurent open. This includes self-pinching in the one-gon and the two-gon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonNormalizationTorusPullback
open PolygonPinching
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
instance torus_open : IsOpenImmersion (torusToComponent K).left := by
  change IsOpenImmersion (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K)
  infer_instance

include h in
/-- The specified node images are outside every Laurent component. -/
theorem node_not_torus (i j : Fin n) (x : Spec (.of K)) :
    (nodeι K n j ≫ q).left x ∉
      Set.range (torusToComponent K ≫ componentι K n i ≫ p).left := by
  let := polygon_lfp K n hn p q h
  intro hx
  have hs : (nodeι K n j ≫ q).left x ∈ C.hom.smoothLocus := by
    change _ ∈ (C.hom.smoothLocus : Set C.left)
    rw [smooth_range K n hn p q h]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  exact ((PolygonNodeLocus.nonsmooth_iff K n hn p q h _).mpr ⟨j, x, rfl⟩) hs

include h in
/-- A normalization component has no extra points over its Laurent open. -/
theorem torus_preimage (i : Fin n) :
    let := torus_isOpenImmersion K n hn p q h i
    (componentι K n i ≫ p).left ⁻¹ᵁ
      (torusToComponent K ≫ componentι K n i ≫ p).left.opensRange =
        (torusToComponent K).left.opensRange := by
  let := torus_isOpenImmersion K n hn p q h i
  ext z
  change (componentι K n i ≫ p).left z ∈
    Set.range (torusToComponent K ≫ componentι K n i ≫ p).left ↔
      z ∈ Set.range (torusToComponent K).left
  constructor
  · intro hz
    rcases ProjectiveLine.torus_or_endpoints K z with ht | ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact ht
    · have he := congrArg (fun f ↦ f.left x) (PolygonNodeIncidence.zero_node K n hn p q h i)
      exact (node_not_torus K n hn p q h i i x (he ▸ hz)).elim
    · let j := (finRotate n).symm i
      have hj : next hn j = i := by
        rw [PolygonCyclicAtlas.next_eq_rotate, Equiv.apply_symm_apply]
      have he := congrArg (fun f ↦ f.left x)
        (PolygonNodeIncidence.infinity_node K n hn p q h j)
      rw [hj] at he
      exact (node_not_torus K n hn p q h i j x (he ▸ hz)).elim
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

include h in
/-- Normalization is unchanged over the full Laurent component. -/
theorem torus_square (i : Fin n) :
    IsPullback (𝟙 (MultiplicativeGroupScheme.gm K).left) (torusToComponent K).left
      (torusToComponent K ≫ componentι K n i ≫ p).left (componentι K n i ≫ p).left := by
  let := torus_isOpenImmersion K n hn p q h i
  exact IsOpenImmersion.isPullback _ _ _ _ (by simp) (torus_preimage K n hn p q h i)

include h in
/-- A different component, including its endpoints, misses a Laurent open. -/
theorem component_torus_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (componentι K n i ≫ p).left)
      (Set.range (torusToComponent K ≫ componentι K n j ≫ p).left) := by
  let := torus_isOpenImmersion K n hn p q h j
  rw [← PolygonComponentImages.closure_torus K n hn p q h i]
  exact (PolygonComponentDistinct.torus_disjoint K n hn p q h hij).closure_left
    (torusToComponent K ≫ componentι K n j ≫ p).left.isOpenEmbedding.isOpenMap.isOpen_range
end FLT.Mazur.PolygonNormalizationTorusPullback
