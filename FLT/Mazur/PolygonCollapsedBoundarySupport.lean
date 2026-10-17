/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOmittedComponentCover

/-!
# The two boundary supports of the collapsed chain

The inverse-image calculation uses complete normalization branches, including
both edges of a two-gon. Each boundary retains precisely its omitted branch.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedBoundarySupport
open PolygonCyclicAtlas PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "F" => fiberIdeal K n (by omega) (normalization K n h)
  (nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega)) i

/-- A fiber point over a node belongs to one of its omitted full branches. -/
theorem chart_support (j : Fin n) (x : PolygonNodeBranches.node K) :
    x ∈ ((F).comap (chart K n h j)).support ↔
      (j ≠ i ∧ x ∈ Set.range (firstBranch K)) ∨
        (finRotate n j ≠ i ∧ x ∈ Set.range (secondBranch K)) := by
  rw [Scheme.IdealSheafData.support_comap]
  change chart K n h j x ∈ ((F).support : Set (polygon K n h).left) ↔ _
  rw [PolygonOmittedComponentCover.support_eq K n h i]
  constructor
  · intro hx
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp hx
    rcases PolygonCyclicNormalizationRanges.component_preimage K n h k.val j z
      ⟨x, hz.symm⟩ with ⟨a, hk, ha⟩ | ⟨a, hk, ha⟩
    · left
      refine ⟨hk ▸ k.property, a, ?_⟩
      apply (chart K n h j).isOpenEmbedding.injective
      rw [← ha, hk] at hz
      exact (congrArg (fun f ↦ f a) (left_componentMap K n h j)).symm.trans hz
    · right
      refine ⟨hk ▸ k.property, a, ?_⟩
      apply (chart K n h j).isOpenEmbedding.injective
      rw [← ha, hk] at hz
      have he := right_componentMap K n h (finRotate n j)
      rw [Equiv.symm_apply_apply] at he
      exact (congrArg (fun f ↦ f a) he).symm.trans hz
  · rintro (⟨hj, a, rfl⟩ | ⟨hj, a, rfl⟩)
    · refine Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ProjectiveLine.left K a, ?_⟩
      exact congrArg (fun f ↦ f a) (left_componentMap K n h j)
    · refine Set.mem_iUnion.mpr
        ⟨⟨finRotate n j, hj⟩, ProjectiveLine.right K a, ?_⟩
      have he := right_componentMap K n h (finRotate n j)
      rw [Equiv.symm_apply_apply] at he
      exact congrArg (fun f ↦ f a) he

/-- At the retained node, only the successor's complete second branch remains. -/
theorem retained_support :
    (((F).comap (chart K n h i)).support : Set (PolygonNodeBranches.node K)) =
      Set.range (secondBranch K) := by
  ext x
  change x ∈ ((F).comap (chart K n h _)).support ↔ _
  rw [chart_support]
  simp only [ne_eq, not_true_eq_false, false_and, false_or,
    (PolygonCyclicNormalizationPullback.successor_ne n h i).symm, not_false_eq_true,
    true_and]

/-- At the predecessor node, only the predecessor's complete first branch remains. -/
theorem predecessor_support :
    (((F).comap (chart K n h ((finRotate n).symm i))).support :
      Set (PolygonNodeBranches.node K)) = Set.range (firstBranch K) := by
  ext x
  change x ∈ ((F).comap (chart K n h _)).support ↔ _
  rw [chart_support]
  simp only [Equiv.apply_symm_apply, ne_eq, not_true_eq_false, false_and, or_false,
    prev_ne h i, not_false_eq_true, true_and]

end FLT.Mazur.PolygonCollapsedBoundarySupport
