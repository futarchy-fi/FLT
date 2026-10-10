/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorBranchIntersections
public import FLT.Mazur.WeierstrassDividedZeroSplitCycleRanges
public import FLT.Mazur.WeierstrassDividedBranchPairSeparation

/-!
# Nonadjacent complete cyclic components are disjoint

The only possible intersections are between cyclic neighbors, including the
wrap from the last component to the original exterior.
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

/-- Numerically ordered nonneighbors have disjoint complete cyclic images. -/
theorem zeroSplitCycleComponent_ordered_disjoint (a b : Fin (2 * s + 3))
    (hab : a.val < b.val) (hgap : a.val + 1 ≠ b.val)
    (hwrap : a.val ≠ 0 ∨ b.val ≠ 2 * s + 2) :
    Disjoint (Set.range (Z a).left) (Set.range (Z b).left) := by
  by_cases ha0 : a.val = 0
  · have he : a = 0 := Fin.ext ha0
    rw [he, zeroSplitCycleComponent_exterior]
    by_cases hb : b.val ≤ s + 1
    · rw [zeroSplitCycleComponent, ite_eq_right (by omega), dite_eq_left hb,
        ProjectiveLine.endpointReversalOver_map_range]
      exact finalZeroExteriorComponent_later_branch_disjoint hπ data D s hs hstart hk hp
        ⟨b.val - 1, by omega⟩ (by dsimp; omega) 0
    · rw [zeroSplitCycleComponent, ite_eq_right (by omega), dite_eq_right hb]
      exact finalZeroExteriorComponent_later_branch_disjoint hπ data D s hs hstart hk hp
        ⟨2 * s + 2 - b.val, by omega⟩ (by dsimp; omega) 1
  · by_cases ha : a.val ≤ s + 1
    · by_cases hb : b.val ≤ s + 1
      · rw [zeroSplitCycleComponent, ite_eq_right ha0, dite_eq_left ha,
          ProjectiveLine.endpointReversalOver_map_range,
          zeroSplitCycleComponent, ite_eq_right (by omega), dite_eq_left hb,
          ProjectiveLine.endpointReversalOver_map_range]
        exact finalBranchComponents_nonadjacent_disjoint hπ data D s hs hk hp
          ⟨a.val - 1, by omega⟩ ⟨b.val - 1, by omega⟩ (by dsimp; omega) 0 0
      · rw [zeroSplitCycleComponent, ite_eq_right ha0, dite_eq_left ha,
          ProjectiveLine.endpointReversalOver_map_range,
          zeroSplitCycleComponent, ite_eq_right (by omega), dite_eq_right hb]
        exact finalBranchComponents_opposite_disjoint hπ data D s hs hk hp
          ⟨a.val - 1, by omega⟩ ⟨2 * s + 2 - b.val, by omega⟩ (by dsimp; omega)
    · have hb : ¬b.val ≤ s + 1 := by omega
      rw [zeroSplitCycleComponent, ite_eq_right ha0, dite_eq_right ha,
        zeroSplitCycleComponent, ite_eq_right (by omega), dite_eq_right hb]
      exact (finalBranchComponents_nonadjacent_disjoint hπ data D s hs hk hp
        ⟨2 * s + 2 - b.val, by omega⟩ ⟨2 * s + 2 - a.val, by omega⟩
        (by dsimp; omega) 1 1).symm

/-- Apart from equality and the two cyclic neighbors, complete components are disjoint. -/
theorem zeroSplitCycleComponent_nonadjacent_disjoint (a b : Fin (2 * s + 3))
    (hab : a ≠ b) (hn : PolygonPinching.next (by omega) a ≠ b)
    (hp' : PolygonPinching.next (by omega) b ≠ a) :
    Disjoint (Set.range (Z a).left) (Set.range (Z b).left) := by
  have ordered (i j : Fin (2 * s + 3)) (hij : i.val < j.val)
      (hij' : PolygonPinching.next (by omega) i ≠ j)
      (hji' : PolygonPinching.next (by omega) j ≠ i) :
      Disjoint (Set.range (Z i).left) (Set.range (Z j).left) := by
    apply zeroSplitCycleComponent_ordered_disjoint hπ data D s hs hstart hk hp i j hij
    · intro he
      apply hij'
      apply Fin.ext
      change (i.val + 1) % (2 * s + 3) = j.val
      rw [he, Nat.mod_eq_of_lt j.isLt]
    · by_contra he
      have hz : i.val = 0 ∧ j.val = 2 * s + 2 := by simpa using he
      apply hji'
      apply Fin.ext
      change (j.val + 1) % (2 * s + 3) = i.val
      rw [show j.val + 1 = 2 * s + 3 by omega, Nat.mod_self, hz.1]
  have hv : a.val ≠ b.val := fun he => hab (Fin.ext he)
  rcases lt_or_gt_of_ne hv with h | h
  · exact ordered a b h hn hp'
  · exact (ordered b a h hp' hn).symm

end FLT.Mazur.WeierstrassDividedDepth
