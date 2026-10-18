/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedGlobalMap
public import FLT.Mazur.WeierstrassDividedRevisedInfinityImage
public import FLT.Mazur.WeierstrassDividedRevisedNodeCoverage

/-!
# The complete original first-order comparison is surjective

The full infinity edge completes both original initial opens. Every retained
and terminal node is filled by its actual normalization and closing correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
/-- Precomposing with an isomorphism preserves the entire image, in any scheme target. -/
theorem revisedComparison_range_of_isIso {X Y Z : Scheme} (e : X ⟶ Y) [IsIso e]
    (f : Y ⟶ Z) : Set.range (e ≫ f) = Set.range f := by
  have hs : Function.Surjective e := (Scheme.homeoOfIso (asIso e)).surjective
  change Set.range (f ∘ e) = _
  rw [Set.range_comp, hs.range_eq, Set.image_univ]

/-- An oriented full-node cover descends to an image inclusion without expanding the target. -/
theorem revisedComparison_oriented_cover {U V X Y : Scheme} (e : X ≅ X) (c : X ⟶ Y)
    (f : U ⟶ Y) (g : V ⟶ Y) (T : Set Y)
    (h : ∀ x : X, (e.hom ≫ c) x ∈ Set.range f ∨ (e.hom ≫ c) x ∈ Set.range g)
    (hf : Set.range f ⊆ T) (hg : Set.range g ⊆ T) : Set.range c ⊆ T := by
  rintro _ ⟨x, rfl⟩
  have hs : Function.Surjective e.hom := (Scheme.homeoOfIso e).surjective
  obtain ⟨z, hz⟩ := hs x
  have hx := h z
  change c (e.hom z) ∈ Set.range f ∨ c (e.hom z) ∈ Set.range g at hx
  rw [hz] at hx
  exact hx.elim (fun hx ↦ hf hx) (fun hx ↦ hg hx)

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "F" => arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "c" => arithmeticRevisedPolygonInitialChart data H 1 j hj u hu
local notation "d" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "O" => twistedRetainedOrientation data H 1

/-- Each full original labeled image lies in the image of the descended global map. -/
theorem arithmeticFirstOriginalRevisedChart_range_subset (i : ArithmeticChartLabel (j + 1)) :
    Set.range (G i) ⊆ Set.range F := by
  rintro _ ⟨x, rfl⟩
  refine ⟨a i x, ?_⟩
  exact congrArg (fun f ↦ f x) (arithmeticFirstOriginalRevisedGlobalMap_chart hπ data H j hj u hu i)

/-- The complete revised infinity edge lies in the original global image. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_infinity_range :
    Set.range (rightBranchOpen Q τ ≫ c false) ⊆ Set.range F := by
  rw [← arithmeticOriginalRevisedTensorInfinityMap_range data H 1 j hj u hu]
  exact arithmeticFirstOriginalRevisedChart_range_subset hπ data H j hj u hu .infinity

/-- Each full initial target node is filled by its original initial and infinity labels. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_initial_range (b : Bool) :
    Set.range (c b) ⊆ Set.range F := by
  apply revisedComparison_oriented_cover (O b) (c b)
    (arithmeticOriginalRevisedInitialMap data H 1 j hj u hu b)
    (rightBranchOpen Q τ ≫ (O b).hom ≫ c b) (Set.range F)
  · exact arithmeticOriginalRevisedInitialMap_edge_cover data H 1 j hj u hu b
  · exact arithmeticFirstOriginalRevisedChart_range_subset hπ data H j hj u hu (.initial b)
  · rw [arithmeticRevisedPolygon_infinity_range]
    exact arithmeticFirstOriginalRevisedGlobalMap_infinity_range hπ data H j hj u hu

/-- Every retained full target node is covered with the actual residual correction included. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_retained_range (i : Fin (j + 1)) (b : Bool) :
    Set.range (d i b) ⊆ Set.range F := by
  have hr : Set.range (G (.retained i b)) = Set.range (d i b) := by
    change Set.range ((arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj i).hom ≫
      (if i.val = j then arithmeticFirstResidualRetainedIso hπ data H j hj u hu b
        else Iso.refl _).hom ≫ (O b).hom ≫ d i b) = _
    rw [revisedComparison_range_of_isIso, revisedComparison_range_of_isIso,
      revisedComparison_range_of_isIso]
  rw [← hr]
  exact arithmeticFirstOriginalRevisedChart_range_subset hπ data H j hj u hu (.retained i b)

/-- The common corrected terminal normalization fills the entire target label zero. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_terminal_range :
    Set.range (arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu) ⊆ Set.range F := by
  have hr : Set.range (G .terminal) =
      Set.range (arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu) := by
    change Set.range ((arithmeticFirstResidualAtlasIso hπ data H j hj u hu .terminal).hom ≫
      arithmeticRevisedPolygonTerminalChart data H 1 j hj u hu) = _
    exact revisedComparison_range_of_isIso _ _
  rw [← hr]
  exact arithmeticFirstOriginalRevisedChart_range_subset hπ data H j hj u hu .terminal

/-- Every point of the independent revised polygon has an original first-order preimage. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_surjective : Function.Surjective F := by
  intro x
  rcases arithmeticRevisedPolygon_named_cover data H 1 j hj u hu x with
    hx | ⟨b, hx⟩ | ⟨i, b, hx⟩
  · exact arithmeticFirstOriginalRevisedGlobalMap_terminal_range hπ data H j hj u hu hx
  · exact arithmeticFirstOriginalRevisedGlobalMap_initial_range hπ data H j hj u hu b hx
  · exact arithmeticFirstOriginalRevisedGlobalMap_retained_range hπ data H j hj u hu i b hx

end FLT.Mazur.WeierstrassDividedDepth
