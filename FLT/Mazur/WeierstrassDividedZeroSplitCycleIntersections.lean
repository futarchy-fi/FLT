/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorBranchIntersections
public import FLT.Mazur.WeierstrassDividedZeroSplitCycleRanges

/-!
# Exact consecutive intersections in the actual cyclic component order

Every zero endpoint meets the infinity endpoint of its successor, and their
complete images intersect only in that original node section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp
local notation "C" => finalBranchComponent hπ data D s hs hk hp
local notation "N" => finalNodeOverSection hπ data D s hs hk hp

/-- Consecutive cyclic component images intersect exactly at their specified original node. -/
theorem zeroSplitCycleComponent_next_range_inter (i : Fin (2 * s + 3)) :
    Set.range (Z i).left ∩
        Set.range (Z (PolygonPinching.next (by omega) i)).left =
      Set.range (N (zeroSplitCycleNodeIndex start s i)).left := by
  by_cases hi : i.val < s + 1
  · have hn : PolygonPinching.next (by omega) i =
        (⟨i.val + 1, by omega⟩ : Fin (2 * s + 3)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by omega)
    rw [hn, zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨i.val, hi⟩,
      ProjectiveLine.endpointReversalOver_map_range]
    by_cases hi0 : i.val = 0
    · have he : i = 0 := Fin.ext hi0
      subst i
      rw [zeroSplitCycleComponent_exterior]
      exact finalZeroExteriorComponent_first_branch_inter hπ data D s hs hstart hk hp 0
    · have he : i = ⟨(i.val - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
      have hr : Set.range (Z i).left = Set.range (C ⟨i.val - 1, by omega⟩ 0).left := by
        rw [zeroSplitCycleComponent, ite_eq_right hi0, dite_eq_left (by omega),
          ProjectiveLine.endpointReversalOver_map_range]
      rw [hr]
      have he' : i = ⟨(⟨i.val, hi⟩ : Fin (s + 1)).val, by omega⟩ := rfl
      have hnode := zeroSplitCycleNodeIndex_first start s ⟨i.val, hi⟩
      rw [← he'] at hnode
      rw [hnode]
      exact finalBranchComponents_successive_range_inter hπ data D s hs hk hp
        ⟨i.val - 1, by omega⟩ ⟨i.val, hi⟩ (by dsimp; omega) 0
  · by_cases hit : i.val = s + 1
    · have he : i = ⟨(⟨s, by omega⟩ : Fin (s + 1)).val + 1, by omega⟩ :=
        Fin.ext hit
      have hn : PolygonPinching.next (by omega) i =
          (⟨2 * s + 2 - (⟨s, by omega⟩ : Fin (s + 1)).val, by omega⟩ :
            Fin (2 * s + 3)) := by
        apply Fin.ext
        change (i.val + 1) % (2 * s + 3) = _
        rw [Nat.mod_eq_of_lt (by omega)]
        dsimp
        omega
      rw [hn, zeroSplitCycleComponent_second]
      have hZ := zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨s, by omega⟩
      rw [← he] at hZ
      rw [hZ, ProjectiveLine.endpointReversalOver_map_range]
      have hN := zeroSplitCycleNodeIndex_terminal start s
      rw [← he] at hN
      rw [hN]
      exact finalBranchComponents_terminal_range_inter hπ data D s hs hk hp
    · by_cases hilast : i.val = 2 * s + 2
      · have hn : PolygonPinching.next (by omega) i = (0 : Fin (2 * s + 3)) := by
          apply Fin.ext
          simp only [PolygonPinching.next_val, Fin.val_zero]
          rw [show i.val + 1 = 2 * s + 3 by omega, Nat.mod_self]
        have he : i = ⟨2 * s + 2 - (0 : Fin (s + 1)).val, by omega⟩ :=
          Fin.ext (by simpa using hilast)
        rw [hn, he, zeroSplitCycleComponent_second, zeroSplitCycleNodeIndex_second,
          zeroSplitCycleComponent_exterior, Set.inter_comm]
        exact finalZeroExteriorComponent_first_branch_inter hπ data D s hs hstart hk hp 1
      · let j : Fin (s + 1) := ⟨2 * s + 1 - i.val, by omega⟩
        let k : Fin (s + 1) := ⟨2 * s + 2 - i.val, by omega⟩
        have he : i = ⟨2 * s + 2 - k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        have hn : PolygonPinching.next (by omega) i =
            (⟨2 * s + 2 - j.val, by omega⟩ : Fin (2 * s + 3)) := by
          apply Fin.ext
          change (i.val + 1) % (2 * s + 3) = _
          rw [Nat.mod_eq_of_lt (by omega)]
          dsimp [j]
          omega
        rw [hn]
        have hZ := zeroSplitCycleComponent_second hπ data D s hs hstart hk hp k
        rw [← he] at hZ
        have hN := zeroSplitCycleNodeIndex_second start s k
        rw [← he] at hN
        rw [hZ, hN, zeroSplitCycleComponent_second, Set.inter_comm]
        exact finalBranchComponents_successive_range_inter hπ data D s hs hk hp
          j k (by dsimp [j, k]; omega) 1

/-- Equal images on consecutive cyclic components are exactly zero/infinity in cyclic order. -/
theorem zeroSplitCycleComponent_next_eq_iff (i : Fin (2 * s + 3))
    (x y : ProjectiveLine.scheme K) :
    (Z i).left x = (Z (PolygonPinching.next (by omega) i)).left y ↔
      ∃ z : Spec (.of K), ProjectiveLine.zero K z = x ∧
        ProjectiveLine.infinity K z = y := by
  exact componentPoint_eq_iff_of_node_inter _ _ _ _ _
    (zeroSplitCycleComponent_point_injective hπ data D s hs hk hp hstart i)
    (zeroSplitCycleComponent_point_injective hπ data D s hs hk hp hstart _)
    (zeroSplitCycleComponent_next_range_inter hπ data D s hs hstart hk hp i)
    (congrArg Over.Hom.left (zeroSplitCycleComponent_zero hπ data D s hs hstart hk hp i))
    (congrArg Over.Hom.left
      (zeroSplitCycleComponent_next_infinity hπ data D s hs hstart hk hp i)) x y

end FLT.Mazur.WeierstrassDividedDepth
