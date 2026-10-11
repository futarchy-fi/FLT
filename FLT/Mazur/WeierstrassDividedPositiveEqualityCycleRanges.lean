/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleRanges
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle

/-!
# The original full images in the equality-depth cycle

Reversing endpoints preserves every component image. The terminal position
contains exactly the last retained conic and the entire original Laurent chart.
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
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R

variable (hp : 2 * (start + s + 1) = depth)
local notation "T" => equalityTerminalOverComponent hπ data D s hs hk hp

variable (hstart : 0 < start)
local notation "C" => positiveEqualityBranchComponent hπ data D s hs hstart hk
local notation "E" => equalityInitialExteriorOverComponent hπ data D s hs hstart hk
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp

/-- Cyclic ordering retains the full exterior, terminal line, and both full branches. -/
theorem positiveEqualityCycleComponent_images :
    (⋃ i : Fin (2 * s + 4), Set.range (Z i).left) =
      Set.range (E).left ∪ (Set.range (T).left ∪
        ⋃ j : Fin (s + 1), ⋃ b : Fin 2, Set.range (C j b).left) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hx⟩
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      rw [he, positiveEqualityCycleComponent_exterior] at hx
      exact Or.inl hx
    · by_cases h : i.val ≤ s + 1
      · rw [positiveEqualityCycleComponent, dite_eq_right hi, dite_eq_left h,
          ProjectiveLine.endpointReversalOver_map_range] at hx
        exact Or.inr (Or.inr ⟨⟨i.val - 1, by omega⟩, 0, hx⟩)
      · by_cases ht : i.val = s + 2
        · have he : i = ⟨s + 2, by omega⟩ := Fin.ext ht
          rw [he, positiveEqualityCycleComponent_terminal,
            ProjectiveLine.endpointReversalOver_map_range] at hx
          exact Or.inr (Or.inl hx)
        · rw [positiveEqualityCycleComponent, dite_eq_right hi, dite_eq_right h,
            dite_eq_right ht] at hx
          exact Or.inr (Or.inr ⟨⟨2 * s + 3 - i.val, by omega⟩, 1, hx⟩)
  · rintro (hx | hx | ⟨j, b, hx⟩)
    · refine ⟨0, ?_⟩
      rwa [positiveEqualityCycleComponent_exterior]
    · refine ⟨⟨s + 2, by omega⟩, ?_⟩
      rwa [positiveEqualityCycleComponent_terminal, ProjectiveLine.endpointReversalOver_map_range]
    · fin_cases b
      · refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
        rwa [positiveEqualityCycleComponent_first, ProjectiveLine.endpointReversalOver_map_range]
      · refine ⟨⟨2 * s + 3 - j.val, by omega⟩, ?_⟩
        rwa [positiveEqualityCycleComponent_second]

/-- Every complete branch component occurs as an unchanged cyclic image. -/
theorem positiveEqualityCycleComponent_contains_branch (j : Fin (s + 1)) (b : Fin 2) :
    ∃ i : Fin (2 * s + 4), Set.range (Z i).left = Set.range (C j b).left := by
  fin_cases b
  · refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
    rw [positiveEqualityCycleComponent_first, ProjectiveLine.endpointReversalOver_map_range]
    rfl
  · refine ⟨⟨2 * s + 3 - j.val, by omega⟩, ?_⟩
    rw [positiveEqualityCycleComponent_second]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
