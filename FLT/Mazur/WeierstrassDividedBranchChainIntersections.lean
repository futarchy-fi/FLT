/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentTerminalIntersection
public import FLT.Mazur.WeierstrassDividedFinalChainPairIntersections

/-!
# Complete cross-level intersections in the original two projective chains

These statements uniformly include the last terminal component and preserve the
original tangent order and marked node sections.
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
local notation "K" => ResidueField R

/-- Successive matching complete chain components meet exactly at their common retained node. -/
theorem finalBranchComponents_successive_range_inter (a b : Fin (s + 1))
    (hab : b.val = a.val + 1) (i : Fin 2) :
    Set.range (finalBranchComponent hπ data D s hs hk hp a i).left ∩
        Set.range (finalBranchComponent hπ data D s hs hk hp b i).left =
      Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (b, i)))) := by
  rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨a.val, by omega⟩ i]
  by_cases hb : b.val < s
  · rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨b.val, hb⟩ i]
    exact finalAdjacentComponents_successive_range_inter hπ data D s hs hk
      ⟨a.val, by omega⟩ ⟨b.val, hb⟩ hab i
  · have he : b = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show b.val = s by omega)
    subst b
    rw [finalBranchComponent_terminal]
    exact finalAdjacent_terminal_successive_range_inter hπ data D s hs hk hp
      ⟨a.val, by omega⟩ (show a.val + 1 = s by omega) i

/-- Successive crossed complete chain components have empty intersection. -/
theorem finalBranchComponents_successive_cross_disjoint (a b : Fin (s + 1))
    (hab : b.val = a.val + 1) (i k : Fin 2) (hik : i ≠ k) :
    Disjoint (Set.range (finalBranchComponent hπ data D s hs hk hp a i).left)
      (Set.range (finalBranchComponent hπ data D s hs hk hp b k).left) := by
  rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨a.val, by omega⟩ i]
  by_cases hb : b.val < s
  · rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨b.val, hb⟩ k]
    exact finalAdjacentComponents_successive_cross_disjoint hπ data D s hs hk
      ⟨a.val, by omega⟩ ⟨b.val, hb⟩ hab i k hik
  · have he : b = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show b.val = s by omega)
    subst b
    rw [finalBranchComponent_terminal]
    exact finalAdjacent_terminal_successive_cross_disjoint hπ data D s hs hk hp
      ⟨a.val, by omega⟩ (show a.val + 1 = s by omega) i k hik

/-- Complete components separated by at least one chain edge are disjoint in either branch. -/
theorem finalBranchComponents_nonadjacent_disjoint (a b : Fin (s + 1))
    (hab : a.val + 2 ≤ b.val) (i k : Fin 2) :
    Disjoint (Set.range (finalBranchComponent hπ data D s hs hk hp a i).left)
      (Set.range (finalBranchComponent hπ data D s hs hk hp b k).left) := by
  rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨a.val, by omega⟩ i]
  by_cases hb : b.val < s
  · rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨b.val, hb⟩ k]
    exact finalAdjacentComponents_nonadjacent_disjoint hπ data D s hs hk
      ⟨a.val, by omega⟩ ⟨b.val, hb⟩ hab i k
  · have he : b = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show b.val = s by omega)
    subst b
    rw [finalBranchComponent_terminal]
    exact finalAdjacent_terminal_nonadjacent_disjoint hπ data D s hs hk hp
      ⟨a.val, by omega⟩ hab i k

/-- Equal images on successive matching components are their original infinity/zero marking. -/
theorem finalBranchComponents_successive_eq_iff (a b : Fin (s + 1))
    (hab : b.val = a.val + 1) (i : Fin 2) (x y : ProjectiveLine.scheme K) :
    (finalBranchComponent hπ data D s hs hk hp a i).left x =
        (finalBranchComponent hπ data D s hs hk hp b i).left y ↔
      ∃ z : Spec (.of K), ProjectiveLine.infinity K z = x ∧
        ProjectiveLine.zero K z = y := by
  have hzero : ProjectiveLine.zero K ≫
      (finalBranchComponent hπ data D s hs hk hp b i).left =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (b, i))) := by
    have H := finalBranchComponent_zero hπ data D s hs hk hp b i
    rw [finalBranchVertex_retained] at H
    exact congrArg (fun f => f.left) H
  have hinfinity : ProjectiveLine.infinity K ≫
      (finalBranchComponent hπ data D s hs hk hp a i).left =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (b, i))) := by
    have H := congrArg (fun f => f.left)
      (finalBranchComponent_infinity hπ data D s hs hk hp a i)
    have he : (⟨a.val + 1, by omega⟩ : Fin (s + 2)) =
        ⟨b.val, by omega⟩ := Fin.ext hab.symm
    rw [he, finalBranchVertex_retained] at H
    exact H
  constructor
  · intro hxy
    have hz : (finalBranchComponent hπ data D s hs hk hp a i).left x ∈
        Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (b, i)))) := by
      rw [← finalBranchComponents_successive_range_inter hπ data D s hs hk hp a b hab i]
      exact ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_, ?_⟩
    · apply finalBranchComponent_point_injective hπ data D s hs hk hp a i
      change (ProjectiveLine.infinity K ≫
        (finalBranchComponent hπ data D s hs hk hp a i).left) z = _
      rw [hinfinity]
      exact hz
    · apply finalBranchComponent_point_injective hπ data D s hs hk hp b i
      change (ProjectiveLine.zero K ≫
        (finalBranchComponent hπ data D s hs hk hp b i).left) z = _
      rw [hzero]
      exact hz.trans hxy
  · rintro ⟨z, rfl, rfl⟩
    exact congrArg (fun f => f z) (hinfinity.trans hzero.symm)

end FLT.Mazur.WeierstrassDividedDepth
