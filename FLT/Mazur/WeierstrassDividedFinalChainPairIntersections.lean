/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSplitComponentInjectivity
public import FLT.Mazur.WeierstrassDividedAdjacentComponentDisjoint

/-!
# Exact opposite-branch intersections in the fixed final chains

Opposite components at each retained level are disjoint. The two final components
meet precisely at the original common terminal node, with their infinity orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- The two complete ordered components at one retained level have no intersection. -/
theorem orderedAdjacentComponents_disjoint (j : ℕ) (hj : j + 1 ≤ n)
    (hk : 2 * (start + j + 1) ≤ depth) (hjNext : j + 2 ≤ n)
    (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
    (r : ℕ) (hr : j + 2 + r ≤ n) :
    Disjoint
      (Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 0))
      (Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr 1)) := by
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h,
      orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h]
    exact adjacentRetainedComponents_disjoint hπ data D j hj hk hjNext hkNext r hr h
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega),
      orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr (by omega)]
    exact adjacentZeroComponents_disjoint hπ data D j hj hk hjNext hkNext r hr (by omega)

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)

/-- The actual fixed-stage adjacent pair still has empty intersection. -/
theorem finalAdjacentComponents_disjoint (j : Fin s) :
    Disjoint (Set.range (finalAdjacentComponent hπ data D s hs hk j 0))
      (Set.range (finalAdjacentComponent hπ data D s hs hk j 1)) := by
  unfold finalAdjacentComponent
  apply componentRange_disjoint_postcomp
  · exact Scheme.Hom.injective _
  · exact orderedAdjacentComponents_disjoint hπ data D _ _ _ _ _ _ _

variable (hp : 2 * (start + s + 1) < depth)

/-- The uniform full terminal pair intersects exactly in the original terminal node. -/
theorem finalTerminalComponents_range_inter :
    Set.range (finalTerminalComponent hπ data D s hs hk hp 0) ∩
        Set.range (finalTerminalComponent hπ data D s hs hk hp 1) =
      Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())) := by
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h,
      finalTerminalComponent_positive hπ data D s hs hk hp h]
    exact terminalComponents_range_inter hπ data D s hs hk hp h
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega),
      finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    exact terminalZeroComponents_range_inter hπ data D s hs hk hp (by omega)

/-- At each level before the terminal one the two full chain components are disjoint. -/
theorem finalBranchComponents_same_level_disjoint (j : Fin s) :
    Disjoint
      (Set.range (finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ 0).left)
      (Set.range (finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ 1).left) := by
  rw [finalBranchComponent_adjacent, finalBranchComponent_adjacent]
  exact finalAdjacentComponents_disjoint hπ data D s hs hk j

/-- The complete final chain components meet at exactly the original terminal node section. -/
theorem finalBranchComponents_terminal_range_inter :
    Set.range (finalBranchComponent hπ data D s hs hk hp ⟨s, by omega⟩ 0).left ∩
        Set.range (finalBranchComponent hπ data D s hs hk hp ⟨s, by omega⟩ 1).left =
      Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())) := by
  rw [finalBranchComponent_terminal, finalBranchComponent_terminal]
  exact finalTerminalComponents_range_inter hπ data D s hs hk hp

/-- Equal images on distinct terminal components are exactly their common infinity marking. -/
theorem finalTerminalComponents_eq_iff
    (x y : ProjectiveLine.scheme K) :
    finalTerminalComponent hπ data D s hs hk hp 0 x =
        finalTerminalComponent hπ data D s hs hk hp 1 y ↔
      ∃ z : Spec (.of K), ProjectiveLine.infinity K z = x ∧
        ProjectiveLine.infinity K z = y := by
  constructor
  · intro hxy
    have hz : finalTerminalComponent hπ data D s hs hk hp 0 x ∈
        Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())) := by
      rw [← finalTerminalComponents_range_inter hπ data D s hs hk hp]
      exact ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_, ?_⟩
    · apply finalTerminalComponent_point_injective hπ data D s hs hk hp 0
      change (ProjectiveLine.infinity K ≫ finalTerminalComponent hπ data D s hs hk hp 0) z = _
      rw [finalTerminalComponent_infinity]
      exact hz
    · apply finalTerminalComponent_point_injective hπ data D s hs hk hp 1
      change (ProjectiveLine.infinity K ≫ finalTerminalComponent hπ data D s hs hk hp 1) z = _
      rw [finalTerminalComponent_infinity]
      exact hz.trans hxy
  · rintro ⟨z, rfl, rfl⟩
    exact congrArg (fun f => f z)
      ((finalTerminalComponent_infinity hπ data D s hs hk hp 0).trans
        (finalTerminalComponent_infinity hπ data D s hs hk hp 1).symm)

end FLT.Mazur.WeierstrassDividedDepth
