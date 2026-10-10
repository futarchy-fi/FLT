/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSplitCycleRanges
public import FLT.Mazur.WeierstrassDividedFinalZeroExteriorRanges

/-!
# The actual split-terminal cyclic components exhaust the original global fiber

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => finalBranchComponent hπ data D s hs hk hp
local notation "E" => finalZeroExteriorOverComponent hπ data D s hs hstart hk
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

local notation "U" => ⋃ i : Fin (2 * s + 3), Set.range (Over.Hom.left (Z i))

/-- Each entire branch-chain component lies in the cyclic image union. -/
theorem zeroSplitCycle_branch_range_subset (j : Fin (s + 1)) (b : Fin 2) :
    Set.range (C j b).left ⊆ U := by
  obtain ⟨i, hi⟩ := zeroSplitCycleComponent_contains_branch hπ data D s hs hstart hk hp j b
  exact hi ▸ Set.subset_iUnion (fun i => Set.range (Z i).left) i

/-- The complete original exterior lies in the cyclic image union. -/
theorem zeroSplitCycle_exterior_range_subset : Set.range (E).left ⊆ U := by
  have H := Set.subset_iUnion (fun i => Set.range (Z i).left) 0
  rwa [zeroSplitCycleComponent_exterior] at H

/-- Every full original retained conic is covered by actual cyclic components. -/
theorem zeroSplitCycle_conic_range_subset (j : Fin (s + 1)) :
    Set.range (retainedConicAt hπ data D (s + 1) hs j.val (by omega) (by omega)) ⊆ U :=
  (finalBranchComponents_cover_conic hπ data D s hs hk hp j).trans
    (Set.union_subset (zeroSplitCycle_branch_range_subset hπ data D s hs hstart hk hp j 0)
      (zeroSplitCycle_branch_range_subset hπ data D s hs hstart hk hp j 1))

/-- Every original adjacent component occurs in the cyclic image union. -/
theorem zeroSplitCycle_adjacent_range_subset (j : Fin s) (b : Fin 2) :
    Set.range (finalAdjacentComponent hπ data D s hs hk j b) ⊆ U := by
  have H := zeroSplitCycle_branch_range_subset hπ data D s hs hstart hk hp
    ⟨j.val, by omega⟩ b
  rw [finalBranchComponent_adjacent] at H
  exact H

/-- The original infinity chart is covered by the cyclic components. -/
theorem zeroSplitCycle_infinity_range_subset :
    Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) ⊆ U := by
  have H := finalZeroExterior_conic_range hπ data D s hs hstart hk
  exact (Set.subset_union_right.trans (le_of_eq H.symm)).trans
    (Set.union_subset (zeroSplitCycle_exterior_range_subset hπ data D s hs hstart hk hp)
      (zeroSplitCycle_conic_range_subset hπ data D s hs hstart hk hp 0))

/-- Every whole retained chart is covered, including the first scale-one chart. -/
theorem zeroSplitCycle_retained_range_subset (j : Fin (s + 1)) :
    Set.range (retainedTensorChartAt hπ data (s + 1) hs j.val (by omega)) ⊆ U := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
    have H := finalZeroExterior_conic_range hπ data D s hs hstart hk
    exact (Set.subset_union_left.trans (le_of_eq H.symm)).trans
      (Set.union_subset (zeroSplitCycle_exterior_range_subset hπ data D s hs hstart hk hp)
        (zeroSplitCycle_conic_range_subset hπ data D s hs hstart hk hp 0))
  | succ j =>
    exact (finalAdjacentComponents_cover_next_chart hπ data D s hs hk ⟨j, by omega⟩).trans
      (Set.union_subset
        (zeroSplitCycle_conic_range_subset hπ data D s hs hstart hk hp ⟨j + 1, hj⟩)
        (Set.union_subset
          (zeroSplitCycle_adjacent_range_subset hπ data D s hs hstart hk hp ⟨j, by omega⟩ 0)
          (zeroSplitCycle_adjacent_range_subset hπ data D s hs hstart hk hp ⟨j, by omega⟩ 1)))

/-- The entire terminal chart is covered by the last two actual chain components. -/
theorem zeroSplitCycle_terminal_range_subset :
    Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) ⊆ U :=
  (finalBranchComponents_cover_terminal hπ data D s hs hk hp).trans
    (Set.union_subset
      (zeroSplitCycle_branch_range_subset hπ data D s hs hstart hk hp ⟨s, by omega⟩ 0)
      (zeroSplitCycle_branch_range_subset hπ data D s hs hstart hk hp ⟨s, by omega⟩ 1))

/-- Every original finite atlas point belongs to an actual full cyclic component. -/
theorem zeroSplitCycleComponent_cover
    (z : finiteGlobalTensorModel hπ data K (s + 1) hs) :
    ∃ i : Fin (2 * s + 3), ∃ x, (Z i).left x = z := by
  have hz : z ∈ U := by
    obtain ⟨i, x, hi, hx⟩ := zeroStartAtlas_cover_without_initial
      hπ data D (by omega) hstart (s + 1) hs z
    have hx' : z ∈ Set.range (globalTensorAtlasMap hπ data K (s + 1) hs i) := ⟨x, hx⟩
    by_cases h0 : i.val = 0
    · have he : i = 0 := Fin.ext h0
      subst i
      exact zeroSplitCycle_infinity_range_subset hπ data D s hs hstart hk hp hx'
    · by_cases h1 : i.val = 1
      · have he : i = Fin.succ 0 := Fin.ext h1
        subst i
        have hr : Set.range (terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) =
            Set.range (globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0)) := by
          rw [← terminalNodeAtlasIso_map hπ data D (s + 1) hs (by omega) hk hp]
          exact (terminalNodeAtlasIso hπ data D (s + 1) hs (by omega) hk hp).hom
            |>.homeomorph.surjective.range_comp
              (globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0))
        exact zeroSplitCycle_terminal_range_subset hπ data D s hs hstart hk hp (hr.symm ▸ hx')
      · let j : Fin (s + 1) := ⟨s + 2 - i.val, by omega⟩
        have he : (⟨s + 1 - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        have H := retainedTensorChartAt_range_index hπ data (s + 1) hs j.val (by omega)
        rw [he] at H
        exact zeroSplitCycle_retained_range_subset hπ data D s hs hstart hk hp j (H.symm ▸ hx')
  simpa only [Set.mem_iUnion, Set.mem_range] using hz

/-- The union of the actual complete cyclic component images is the whole global fiber. -/
theorem zeroSplitCycleComponent_iUnion_range : U = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, x, hx⟩ := zeroSplitCycleComponent_cover hπ data D s hs hstart hk hp z
  exact Set.mem_iUnion.mpr ⟨i, x, hx⟩

end FLT.Mazur.WeierstrassDividedDepth
