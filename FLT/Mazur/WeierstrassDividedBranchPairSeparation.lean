/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedBranchChainIntersections

/-!
# Uniform separation of the two original projective chains

Opposite branches can meet only at their common terminal level. Within one
branch, only consecutive distinct components can meet.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "C" => finalBranchComponent hπ data D s hs hk hp

/-- Distinct levels on opposite branches have disjoint complete images. -/
theorem finalBranchComponents_cross_level_disjoint (a b : Fin (s + 1))
    (hab : a ≠ b) (i k : Fin 2) (hik : i ≠ k) :
    Disjoint (Set.range (C a i).left) (Set.range (C b k).left) := by
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · by_cases he : b.val = a.val + 1
    · exact finalBranchComponents_successive_cross_disjoint hπ data D s hs hk hp a b he i k hik
    · exact finalBranchComponents_nonadjacent_disjoint hπ data D s hs hk hp a b (by omega) i k
  · by_cases he : a.val = b.val + 1
    · exact (finalBranchComponents_successive_cross_disjoint hπ data D s hs hk hp
        b a he k i hik.symm).symm
    · exact (finalBranchComponents_nonadjacent_disjoint hπ data D s hs hk hp
        b a (by omega) k i).symm

/-- Opposite complete branches meet only if both components are terminal. -/
theorem finalBranchComponents_opposite_disjoint (a b : Fin (s + 1))
    (hab : a.val ≠ s ∨ b.val ≠ s) :
    Disjoint (Set.range (C a 0).left) (Set.range (C b 1).left) := by
  by_cases he : a = b
  · subst b
    have ha : a.val < s := by omega
    exact finalBranchComponents_same_level_disjoint hπ data D s hs hk hp ⟨a.val, ha⟩
  · exact finalBranchComponents_cross_level_disjoint hπ data D s hs hk hp a b he 0 1
      (by decide)

/-- Nonconsecutive distinct components on a fixed branch are disjoint in either order. -/
theorem finalBranchComponents_separated_disjoint (a b : Fin (s + 1))
    (hab : a ≠ b) (hnext : b.val ≠ a.val + 1) (hprev : a.val ≠ b.val + 1)
    (i : Fin 2) : Disjoint (Set.range (C a i).left) (Set.range (C b i).left) := by
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · exact finalBranchComponents_nonadjacent_disjoint hπ data D s hs hk hp a b (by omega) i i
  · exact (finalBranchComponents_nonadjacent_disjoint hπ data D s hs hk hp
      b a (by omega) i i).symm

end FLT.Mazur.WeierstrassDividedDepth
