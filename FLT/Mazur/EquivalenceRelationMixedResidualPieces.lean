/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualOpen

/-!
# Exhaustive residual pieces for arbitrary independent mixed tests

The residual open and all label-embedding graphs form a finite disjoint open
cover after any original mixed test. In particular no equal-size or common-label
replacement of the original relation is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  {T : Scheme.{0}} (z : T ⟶ relation p q I J o o')

/-- The actual graph image on an arbitrary original mixed test. -/
def mixedEmbeddingTestOpen (ι : J ↪ I) : T.Opens := by
  let _ := subframeGraph_isOpenImmersion e o o' ι
  exact z ⁻¹ᵁ (subframeGraph e o o' ι).opensRange

omit [(source p q J o').IsSeparated] in
/-- Graph membership retains its original label embedding. -/
theorem mem_mixedEmbeddingTestOpen (ι : J ↪ I) (x : T) :
    x ∈ mixedEmbeddingTestOpen e o o' z ι ↔
      z x ∈ Set.range (subframeGraph e o o' ι) := Iff.rfl

omit [Etale p] [(source p q J o').IsSeparated] in
/-- The comparison image is exactly the union of every embedding graph. -/
theorem mem_embeddingComparison_range (x : relation p q I J o o') :
    x ∈ Set.range (embeddingComparison e o o') ↔
      ∃ ι : J ↪ I, x ∈ Set.range (subframeGraph e o o' ι) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨ι, a⟩, rfl⟩ := (sigmaMk
      (fun _ : J ↪ I ↦ source p q I o)).surjective y
    refine ⟨ι, a, ?_⟩
    rw [sigmaMk_mk]
    exact (congrArg (fun f ↦ f a) (component_embeddingComparison e o o' ι)).symm
  · rintro ⟨ι, a, rfl⟩
    refine ⟨Sigma.ι (fun _ : J ↪ I ↦ source p q I o) ι a, ?_⟩
    exact congrArg (fun f ↦ f a) (component_embeddingComparison e o o' ι)

/-- Membership in the residual part excludes every original embedding piece. -/
theorem mem_mixedResidualTestOpen (x : T) :
    x ∈ mixedResidualTestOpen e o o' z ↔
      ∀ ι : J ↪ I, x ∉ mixedEmbeddingTestOpen e o o' z ι := by
  change z x ∉ Set.range (embeddingComparison e o o') ↔ _
  rw [mem_embeddingComparison_range]
  simp only [not_exists, mem_mixedEmbeddingTestOpen]

/-- Index every retained original branch, keeping the entire residual part as one piece. -/
def mixedResidualBranchOpen : Option (J ↪ I) → T.Opens
  | none => mixedResidualTestOpen e o o' z
  | some ι => mixedEmbeddingTestOpen e o o' z ι

/-- Every original test point occurs in a retained branch. -/
theorem mixedResidualBranchOpen_covers (x : T) :
    ∃ a, x ∈ mixedResidualBranchOpen e o o' z a := by
  classical
  by_cases h : ∃ ι, x ∈ mixedEmbeddingTestOpen e o o' z ι
  · obtain ⟨ι, hι⟩ := h
    exact ⟨some ι, hι⟩
  · exact ⟨none, (mem_mixedResidualTestOpen e o o' z x).mpr (by simpa using h)⟩

/-- Independent mixed branches remain disjoint under every test restriction. -/
theorem mixedResidualBranchOpen_disjoint (a b : Option (J ↪ I)) (h : a ≠ b) :
    Disjoint (mixedResidualBranchOpen e o o' z a : Set T)
      (mixedResidualBranchOpen e o o' z b : Set T) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  cases a with
  | none =>
    cases b with
    | none => exact h rfl
    | some ι => exact (mem_mixedResidualTestOpen e o o' z x).mp ha ι hb
  | some ι =>
    cases b with
    | none => exact (mem_mixedResidualTestOpen e o o' z x).mp hb ι ha
    | some κ =>
      exact Set.disjoint_left.mp (subframeGraph_disjoint e o o' ι κ
        (fun he ↦ h (congrArg some he))) ha hb

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
