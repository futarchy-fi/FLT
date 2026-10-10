/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# The complete images retained by cyclic ordering

The cyclic list has exactly the union of the original exterior and both
complete branch chains. Endpoint reversal loses no points of any component.
This is not yet an assertion that the images exhaust the whole model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "C" => finalBranchComponent hπ data D s hs hk hp
local notation "E" => finalZeroExteriorOverComponent hπ data D s hs hstart hk
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- Cyclic ordering preserves exactly the full images of the exterior and both chains. -/
theorem zeroSplitCycleComponent_images :
    (⋃ i : Fin (2 * s + 3), Set.range (Z i).left) =
      Set.range (E).left ∪ ⋃ j : Fin (s + 1), ⋃ b : Fin 2, Set.range (C j b).left := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hx⟩
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      rw [he, zeroSplitCycleComponent_exterior] at hx
      exact Or.inl hx
    · by_cases h : i.val ≤ s + 1
      · rw [zeroSplitCycleComponent, ite_eq_right hi, dite_eq_left h,
          ProjectiveLine.endpointReversalOver_map_range] at hx
        exact Or.inr ⟨⟨i.val - 1, by omega⟩, 0, hx⟩
      · rw [zeroSplitCycleComponent, ite_eq_right hi, dite_eq_right h] at hx
        exact Or.inr ⟨⟨2 * s + 2 - i.val, by omega⟩, 1, hx⟩
  · rintro (hx | ⟨j, b, hx⟩)
    · refine ⟨0, ?_⟩
      rwa [zeroSplitCycleComponent_exterior]
    · fin_cases b
      · refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
        rwa [zeroSplitCycleComponent_first, ProjectiveLine.endpointReversalOver_map_range]
      · refine ⟨⟨2 * s + 2 - j.val, by omega⟩, ?_⟩
        rwa [zeroSplitCycleComponent_second]

/-- Each original component image is retained by an actual cyclic component. -/
theorem zeroSplitCycleComponent_contains_branch (j : Fin (s + 1)) (b : Fin 2) :
    ∃ i : Fin (2 * s + 3), Set.range (Z i).left = Set.range (C j b).left := by
  fin_cases b
  · refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
    rw [zeroSplitCycleComponent_first, ProjectiveLine.endpointReversalOver_map_range]
    rfl
  · exact ⟨⟨2 * s + 2 - j.val, by omega⟩,
      congrArg (fun f => Set.range f.left)
        (zeroSplitCycleComponent_second hπ data D s hs hstart hk hp j)⟩

end FLT.Mazur.WeierstrassDividedDepth
