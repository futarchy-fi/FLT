/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.WeierstrassDividedFinalRetainedConic
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

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

/-- The complete conic used in the terminal gluing is the last original retained conic. -/
theorem laurentTerminalOriginalConic_eq_retained :
    laurentTerminalOriginalConic hπ data D s hs hk =
      retainedConicAt hπ data D (s + 1) hs s (by omega) hk := by
  rw [retainedConicAt_original hπ data D s hs 0 hs hk]
  by_cases h : 0 < start + s
  · rw [laurentTerminalOriginalConic_positive hπ data D s hs hk h,
      orderedRetainedConic_positive hπ data D s hs 0 hs hk h,
      olderGlobalMiddleConic, olderGlobalTensorChart_zero_retention]
  · rw [laurentTerminalOriginalConic_zero hπ data D s hs hk (by omega),
      orderedRetainedConic_zero hπ data D s hs 0 hs hk (by omega),
      olderGlobalZeroConic, olderGlobalZeroSuccessiveChart,
      olderGlobalTensorChart_zero_retention, WeierstrassSuccessiveX.zeroResidueConicImmersion,
      Category.assoc]

variable (hp : 2 * (start + s + 1) = depth)
local notation "T" => equalityTerminalOverComponent hπ data D s hs hk hp

/-- The terminal projective line contains precisely the full final conic and Laurent chart. -/
theorem equalityTerminalOverComponent_range : Set.range (T).left =
    Set.range (retainedConicAt hπ data D (s + 1) hs s (by omega) hk) ∪
      Set.range (terminalLaurentChart hπ data D (s + 1) hs (by omega) hk hp) := by
  change Set.range (laurentTerminalProjectiveComponent hπ data D s hs hk hp) = _
  rw [laurentTerminalProjectiveComponent_range, laurentTerminalOriginalConic_eq_retained]
  rfl

variable (hstart : start = 0)
local notation "C" => finalAdjacentOverComponent hπ data D s hs hk
local notation "E" => finalZeroExteriorOverComponent hπ data D s hs hstart hk
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- Cyclic ordering retains the full exterior, terminal line, and both adjacent chains. -/
theorem zeroEqualityCycleComponent_images :
    (⋃ i : Fin (2 * s + 2), Set.range (Z i).left) =
      Set.range (E).left ∪ (Set.range (T).left ∪
        ⋃ j : Fin s, ⋃ b : Fin 2, Set.range (C j b).left) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hx⟩
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      rw [he, zeroEqualityCycleComponent_exterior] at hx
      exact Or.inl hx
    · by_cases h : i.val ≤ s
      · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_left h,
          ProjectiveLine.endpointReversalOver_map_range] at hx
        exact Or.inr (Or.inr ⟨⟨i.val - 1, by omega⟩, 0, hx⟩)
      · by_cases ht : i.val = s + 1
        · have he : i = ⟨s + 1, by omega⟩ := Fin.ext ht
          rw [he, zeroEqualityCycleComponent_terminal,
            ProjectiveLine.endpointReversalOver_map_range] at hx
          exact Or.inr (Or.inl hx)
        · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_right h,
            dite_eq_right ht] at hx
          exact Or.inr (Or.inr ⟨⟨2 * s + 1 - i.val, by omega⟩, 1, hx⟩)
  · rintro (hx | hx | ⟨j, b, hx⟩)
    · refine ⟨0, ?_⟩
      rwa [zeroEqualityCycleComponent_exterior]
    · refine ⟨⟨s + 1, by omega⟩, ?_⟩
      rwa [zeroEqualityCycleComponent_terminal, ProjectiveLine.endpointReversalOver_map_range]
    · fin_cases b
      · refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
        rwa [zeroEqualityCycleComponent_first, ProjectiveLine.endpointReversalOver_map_range]
      · refine ⟨⟨2 * s + 1 - j.val, by omega⟩, ?_⟩
        rwa [zeroEqualityCycleComponent_second]

/-- Every complete adjacent component occurs as an unchanged cyclic image. -/
theorem zeroEqualityCycleComponent_contains_adjacent (j : Fin s) (b : Fin 2) :
    ∃ i : Fin (2 * s + 2), Set.range (Z i).left = Set.range (C j b).left := by
  fin_cases b
  · refine ⟨⟨j.val + 1, by omega⟩, ?_⟩
    rw [zeroEqualityCycleComponent_first, ProjectiveLine.endpointReversalOver_map_range]
    rfl
  · refine ⟨⟨2 * s + 1 - j.val, by omega⟩, ?_⟩
    rw [zeroEqualityCycleComponent_second]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
