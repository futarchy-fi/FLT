/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainInteriorCharts
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The full boundary and interior atlas covers the collapsed chain

The cover consists of two affine lines and the unchanged interior nodes.
Component maps jointly detect morphisms to arbitrary target schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainOpenCover
open PolygonCyclicAtlas PolygonCollapsedChainModel
open PolygonCollapsedChainBoundaryCharts PolygonCollapsedChainInteriorCharts
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

/-- The retained and predecessor boundaries together with all interior nodes. -/
abbrev ChartIndex := Bool ⊕ {j : Fin n // j ≠ i ∧ finRotate n j ≠ i}

/-- The actual affine scheme of each chart. -/
def chartScheme : ChartIndex n i → Scheme
  | .inl _ => ProjectiveLine.chart K
  | .inr _ => PolygonNodeBranches.node K

/-- The chart map preserves the original boundary halves and full interior nodes. -/
def chartMap : (a : ChartIndex n i) → chartScheme K n i a ⟶ chain K n h i
  | .inl false => retainedBoundary K n h i
  | .inl true => predecessorBoundary K n h i
  | .inr j => interior K n h i j.val j.property.1 j.property.2

instance chartMap_isOpenImmersion (a : ChartIndex n i) :
    IsOpenImmersion (chartMap K n h i a) := by
  rcases a with b | j
  · cases b <;> dsimp [chartMap] <;> infer_instance
  · dsimp [chartMap]
    infer_instance

/-- No points are lost by replacing the boundary restrictions by their whole branches. -/
theorem covers (x : chain K n h i) : ∃ a y, chartMap K n h i a y = x := by
  obtain ⟨j, z, hz⟩ := charts_cover K n h ((chainIdeal K n h i).subschemeι x)
  by_cases hj : j = i
  · subst j
    obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
      (retained_isPullback K n h i) z x hz
    exact ⟨.inl false, a, ha⟩
  · by_cases hs : finRotate n j = i
    · have he : j = (finRotate n).symm i := (finRotate n).injective (by
        rw [hs, Equiv.apply_symm_apply])
      subst j
      obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
        (predecessor_isPullback K n h i) z x hz
      exact ⟨.inl true, a, ha⟩
    · obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback
        (interior_isPullback K n h i j hj hs) z x hz
      exact ⟨.inr ⟨j, hj, hs⟩, a, ha⟩

/-- The intrinsic affine boundary and whole-node open cover of the global chain. -/
def cover : (chain K n h i).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (ChartIndex n i)
    (chartScheme K n i) (chartMap K n h i) (covers K n h i) (fun _ ↦ inferInstance)

/-- The omitted complete components detect maps from the chain to any scheme. -/
theorem hom_ext {Y : Scheme} (d e : chain K n h i ⟶ Y)
    (he : ∀ (j : Fin n) (hj : j ≠ i),
      component K n h i hj ≫ d = component K n h i hj ≫ e) : d = e := by
  apply (cover K n h i).hom_ext
  intro a
  rcases a with b | j
  · cases b
    · change retainedBoundary K n h i ≫ d = retainedBoundary K n h i ≫ e
      rw [retainedBoundary, Category.assoc, Category.assoc, he]
    · change predecessorBoundary K n h i ≫ d = predecessorBoundary K n h i ≫ e
      rw [predecessorBoundary, Category.assoc, Category.assoc, he]
  · change interior K n h i j.val j.property.1 j.property.2 ≫ d =
      interior K n h i j.val j.property.1 j.property.2 ≫ e
    apply NodePinchingDescent.hom_ext K
    · rw [first_interior_assoc, first_interior_assoc]
      rw [he]
    · rw [second_interior_assoc, second_interior_assoc]
      rw [he]

end FLT.Mazur.PolygonCollapsedChainOpenCover
