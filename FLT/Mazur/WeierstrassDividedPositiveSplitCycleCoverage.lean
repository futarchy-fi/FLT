/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitCycleRanges
public import FLT.Mazur.WeierstrassDividedInitialChartCoverage
public import FLT.Mazur.WeierstrassDividedFinalInitialCoverage
public import FLT.Mazur.WeierstrassDividedFinalChainCoverage

/-!
# The actual positive-start strict cyclic components exhaust the original global fiber

Every original finite chart is covered by the actual complete projective
components. This is a point-coverage theorem, not a scheme pushout assertion.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => finalAdjacentOverComponent hπ data D s hs hk
local notation "B" => finalBranchComponent hπ data D s hs hk hp
local notation "E" => equalityInitialExteriorOverComponent hπ data D s hs hstart hk
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp

local notation "U" => ⋃ i : Fin (2 * s + 5), Set.range (Over.Hom.left (Z i))

/-- Every complete strict branch component lies in the cyclic image union. -/
theorem positiveSplitCycle_branch_range_subset (j : Fin (s + 1)) (b : Fin 2) :
    Set.range (B j b).left ⊆ U := by
  obtain ⟨i, hi⟩ := positiveSplitCycleComponent_contains_branch
    hπ data D s hs hstart hk hp ⟨j.val + 1, by omega⟩ b
  rw [positiveSplitBranchComponent_tail] at hi
  exact hi ▸ Set.subset_iUnion (fun i => Set.range (Z i).left) i

/-- Every whole adjacent component retains its place in the cyclic image union. -/
theorem positiveSplitCycle_adjacent_range_subset (j : Fin s) (b : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk j b) ⊆ U := by
  have H := positiveSplitCycle_branch_range_subset hπ data D s hs hstart hk hp
    ⟨j.val, by omega⟩ b
  rw [finalBranchComponent_adjacent] at H
  exact H

/-- Each complete initial component also occurs in the cyclic image union. -/
theorem positiveSplitCycle_initial_range_subset (b : Fin 2) :
    Set.range (finalInitialComponent hπ data D s hs hstart hk b) ⊆ U := by
  obtain ⟨i, hi⟩ := positiveSplitCycleComponent_contains_branch
    hπ data D s hs hstart hk hp 0 b
  rw [positiveSplitBranchComponent_initial] at hi
  exact hi ▸ Set.subset_iUnion (fun i => Set.range (Z i).left) i

/-- The complete original exterior lies in the cyclic image union. -/
theorem positiveSplitCycle_exterior_range_subset : Set.range (E).left ⊆ U := by
  have H := Set.subset_iUnion (fun i => Set.range (Z i).left) 0
  rwa [positiveSplitCycleComponent_exterior] at H

/-- Every full retained conic lies in the two actual strict branch components. -/
theorem positiveSplitCycle_conic_range_subset (j : Fin (s + 1)) :
    Set.range (retainedConicAt hπ data D (s + 1) hs j.val (by omega) (by omega)) ⊆ U :=
  (finalBranchComponents_cover_conic hπ data D s hs hk hp j).trans
    (Set.union_subset (positiveSplitCycle_branch_range_subset hπ data D s hs hstart hk hp j 0)
      (positiveSplitCycle_branch_range_subset hπ data D s hs hstart hk hp j 1))

/-- The original infinity chart is covered by the cyclic components. -/
theorem positiveSplitCycle_infinity_range_subset :
    Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) ⊆ U := by
  have H := initialOrientedToGlobal_range hπ data D (s + 1) hs hstart
    (show 2 * start ≤ depth by omega) (by omega)
  exact (Set.subset_union_right.trans (le_of_eq H.symm)).trans
    (positiveSplitCycle_exterior_range_subset hπ data D s hs hstart hk hp)

/-- The original initial tensor chart is covered by the exterior and initial components. -/
theorem positiveSplitCycle_initial_chart_range_subset :
    Set.range (globalInitialTensorChart hπ data K (s + 1) hs) ⊆ U := by
  rw [← initialGlobalIncidenceConic_cover hπ data D (s + 1) hs hstart (by omega)]
  apply Set.union_subset
  · have H := initialOrientedToGlobal_range hπ data D (s + 1) hs hstart
      (show 2 * start ≤ depth by omega) (by omega)
    exact (Set.subset_union_left.trans (le_of_eq H.symm)).trans
      (positiveSplitCycle_exterior_range_subset hπ data D s hs hstart hk hp)
  · exact (finalInitialComponents_cover_conic hπ data D s hs hstart hk).trans
      (Set.union_subset
        (positiveSplitCycle_initial_range_subset hπ data D s hs hstart hk hp 0)
        (positiveSplitCycle_initial_range_subset hπ data D s hs hstart hk hp 1))

/-- Every whole retained chart is covered, including the first positive-scale chart. -/
theorem positiveSplitCycle_retained_range_subset (j : Fin (s + 1)) :
    Set.range (retainedTensorChartAt hπ data (s + 1) hs j.val (by omega)) ⊆ U := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
    exact (finalInitialComponents_cover_first_chart hπ data D s hs hstart hk).trans
      (Set.union_subset
        (positiveSplitCycle_conic_range_subset hπ data D s hs hstart hk hp 0)
        (Set.union_subset
          (positiveSplitCycle_initial_range_subset hπ data D s hs hstart hk hp 0)
          (positiveSplitCycle_initial_range_subset hπ data D s hs hstart hk hp 1)))
  | succ j =>
    exact (finalAdjacentComponents_cover_next_chart hπ data D s hs hk ⟨j, by omega⟩).trans
      (Set.union_subset
        (positiveSplitCycle_conic_range_subset hπ data D s hs hstart hk hp ⟨j + 1, hj⟩)
        (Set.union_subset
          (positiveSplitCycle_adjacent_range_subset hπ data D s hs hstart hk hp ⟨j, by omega⟩ 0)
          (positiveSplitCycle_adjacent_range_subset
            hπ data D s hs hstart hk hp ⟨j, by omega⟩ 1)))

/-- The original terminal chart lies in the two complete original terminal branches. -/
theorem positiveSplitCycle_terminal_range_subset :
    Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) ⊆ U :=
  (finalBranchComponents_cover_terminal hπ data D s hs hk hp).trans
    (Set.union_subset
      (positiveSplitCycle_branch_range_subset hπ data D s hs hstart hk hp ⟨s, by omega⟩ 0)
      (positiveSplitCycle_branch_range_subset hπ data D s hs hstart hk hp ⟨s, by omega⟩ 1))

/-- Every original finite atlas point belongs to an actual full cyclic component. -/
theorem positiveSplitCycleComponent_cover
    (z : finiteGlobalTensorModel hπ data K (s + 1) hs) :
    ∃ i : Fin (2 * s + 5), ∃ x, (Z i).left x = z := by
  have hz : z ∈ U := by
    obtain ⟨i, x, hx⟩ := globalTensorAtlas_cover hπ data K (s + 1) hs z
    have hx' : z ∈ Set.range (globalTensorAtlasMap hπ data K (s + 1) hs i) := ⟨x, hx⟩
    by_cases h0 : i.val = 0
    · have he : i = 0 := Fin.ext h0
      subst i
      exact positiveSplitCycle_infinity_range_subset hπ data D s hs hstart hk hp hx'
    · by_cases h1 : i.val = 1
      · have he : i = Fin.succ 0 := Fin.ext h1
        subst i
        have hr : Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) =
            Set.range (globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0)) := by
          rw [← terminalNodeAtlasIso_map hπ data D (s + 1) hs (by omega) hk hp]
          exact (terminalNodeAtlasIso hπ data D (s + 1) hs (by omega) hk hp).hom
            |>.homeomorph.surjective.range_comp
              (globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0))
        exact positiveSplitCycle_terminal_range_subset
          hπ data D s hs hstart hk hp (hr.symm ▸ hx')
      · by_cases hi : i.val = s + 3
        · have he : i = ⟨s + 3, by omega⟩ := Fin.ext hi
          rw [he] at hx'
          have H := globalInitialTensorChart_range_index hπ data K (s + 1) hs
          exact positiveSplitCycle_initial_chart_range_subset
            hπ data D s hs hstart hk hp (H.symm ▸ hx')
        · let j : Fin (s + 1) := ⟨s + 2 - i.val, by omega⟩
          have he : (⟨s + 1 - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) = i := by
            apply Fin.ext
            dsimp [j]
            omega
          have H := retainedTensorChartAt_range_index hπ data (s + 1) hs j.val (by omega)
          rw [he] at H
          exact positiveSplitCycle_retained_range_subset
            hπ data D s hs hstart hk hp j (H.symm ▸ hx')
  simpa only [Set.mem_iUnion, Set.mem_range] using hz

/-- The union of the actual complete cyclic component images is the whole global fiber. -/
theorem positiveSplitCycleComponent_iUnion_range : U = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, x, hx⟩ := positiveSplitCycleComponent_cover hπ data D s hs hstart hk hp z
  exact Set.mem_iUnion.mpr ⟨i, x, hx⟩

end FLT.Mazur.WeierstrassDividedDepth
