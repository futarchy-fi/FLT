/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorTerminalIntersection
public import FLT.Mazur.WeierstrassDividedBranchChainIntersections

/-!
# Exact intersections of the exterior with both complete projective chains

The first components meet their corresponding original exterior endpoints.
Every later component is disjoint, including the terminal successor.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Injective component maps with one exact node intersection identify precisely its markings. -/
theorem componentPoint_eq_iff_of_node_inter {K : Type u} [Field K] {X : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ X) (n : Spec (.of K) ⟶ X)
    (a b : Spec (.of K) ⟶ ProjectiveLine.scheme K)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hi : Set.range f ∩ Set.range g = Set.range n)
    (ha : a ≫ f = n) (hb : b ≫ g = n) (x y : ProjectiveLine.scheme K) :
    f x = g y ↔ ∃ z : Spec (.of K), a z = x ∧ b z = y := by
  constructor
  · intro hxy
    have hz : f x ∈ Set.range n := by
      rw [← hi]
      exact ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    obtain ⟨z, hz⟩ := hz
    refine ⟨z, hf ?_, hg ?_⟩
    · change (a ≫ f) z = _
      rw [ha]
      exact hz
    · change (b ≫ g) z = _
      rw [hb]
      exact hz.trans hxy
  · rintro ⟨z, rfl, rfl⟩
    exact congrArg (fun m => m z) (ha.trans hb.symm)

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "E" => Over.Hom.left
  (finalZeroExteriorOverComponent hπ data D s hs hstart hk)
local notation "C" => finalBranchComponent hπ data D s hs hk hp
local notation "N" => finalNodeOverSection hπ data D s hs hk hp

/-- The exterior meets each first complete chain component exactly at its original initial node. -/
theorem finalZeroExteriorComponent_first_branch_inter (i : Fin 2) :
    Set.range E ∩ Set.range (C 0 i).left =
      Set.range ((N (.inl (.inr (0, i)))).left) := by
  by_cases hs0 : 0 < s
  · have H : C 0 i = finalAdjacentOverComponent hπ data D s hs hk ⟨0, hs0⟩ i := by
      simp only [finalBranchComponent, Fin.val_zero, dite_eq_left hs0]
    rw [H]
    exact finalZeroExteriorComponent_first_adjacent_inter hπ data D s hs hstart hk hs0 hp i
  · have he : s = 0 := by omega
    subst s
    have H : finalBranchComponent hπ data D 0 hs hk hp 0 i =
        finalTerminalOverComponent hπ data D 0 hs hk hp i := by
      simp only [finalBranchComponent, Fin.val_zero, lt_self_iff_false, dite_false]
    rw [H]
    fin_cases i
    · exact finalZeroExteriorComponent_first_terminal_inter hπ data D hs hstart hk hp
    · exact finalZeroExteriorComponent_second_terminal_inter hπ data D hs hstart hk hp

/-- The exterior is disjoint from every positive-level complete component in either chain. -/
theorem finalZeroExteriorComponent_later_branch_disjoint (j : Fin (s + 1))
    (hj : 0 < j.val) (i : Fin 2) :
    Disjoint (Set.range E) (Set.range (C j i).left) := by
  by_cases hj' : j.val < s
  · rw [finalBranchComponent_adjacent hπ data D s hs hk hp ⟨j.val, hj'⟩ i]
    exact finalZeroExteriorComponent_later_adjacent_disjoint hπ data D s hs hstart hk
      ⟨j.val, hj'⟩ hj i
  · have he : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show j.val = s by omega)
    subst j
    rw [finalBranchComponent_terminal]
    exact finalZeroExteriorComponent_later_terminal_disjoint hπ data D s hs hk hp
      hstart hj i

/-- The first-chain equality keeps zero on both original component parameterizations. -/
theorem finalZeroExteriorComponent_first_branch_eq_iff (x y : ProjectiveLine.scheme K) :
    E x = (C 0 0).left y ↔
      ∃ z : Spec (.of K), ProjectiveLine.zero K z = x ∧ ProjectiveLine.zero K z = y := by
  have hE : ProjectiveLine.zero K ≫ E = (N (.inl (.inr (0, 0)))).left :=
    congrArg (fun f => f.left)
      (finalZeroExteriorOverComponent_zero hπ data D s hs hstart hk hp)
  have hC : ProjectiveLine.zero K ≫ (C 0 0).left =
      (N (.inl (.inr (0, 0)))).left := by
    have H := finalBranchComponent_zero hπ data D s hs hk hp 0 0
    rw [finalBranchVertex_retained] at H
    exact congrArg (fun f => f.left) H
  exact componentPoint_eq_iff_of_node_inter E (C 0 0).left
    (N (.inl (.inr (0, 0)))).left (ProjectiveLine.zero K) (ProjectiveLine.zero K)
    (finalZeroExteriorComponent_point_injective hπ data D s hs hk hstart)
    (finalBranchComponent_point_injective hπ data D s hs hk hp 0 0)
    (finalZeroExteriorComponent_first_branch_inter hπ data D s hs hstart hk hp 0) hE hC x y

/-- The opposite chain meets the original infinity marking of the exterior at its zero marking. -/
theorem finalZeroExteriorComponent_second_branch_eq_iff (x y : ProjectiveLine.scheme K) :
    E x = (C 0 1).left y ↔
      ∃ z : Spec (.of K), ProjectiveLine.infinity K z = x ∧ ProjectiveLine.zero K z = y := by
  have hE : ProjectiveLine.infinity K ≫ E = (N (.inl (.inr (0, 1)))).left :=
    congrArg (fun f => f.left)
      (finalZeroExteriorOverComponent_infinity hπ data D s hs hstart hk hp)
  have hC : ProjectiveLine.zero K ≫ (C 0 1).left =
      (N (.inl (.inr (0, 1)))).left := by
    have H := finalBranchComponent_zero hπ data D s hs hk hp 0 1
    rw [finalBranchVertex_retained] at H
    exact congrArg (fun f => f.left) H
  exact componentPoint_eq_iff_of_node_inter E (C 0 1).left
    (N (.inl (.inr (0, 1)))).left (ProjectiveLine.infinity K) (ProjectiveLine.zero K)
    (finalZeroExteriorComponent_point_injective hπ data D s hs hk hstart)
    (finalBranchComponent_point_injective hπ data D s hs hk hp 0 1)
    (finalZeroExteriorComponent_first_branch_inter hπ data D s hs hstart hk hp 1) hE hC x y

end FLT.Mazur.WeierstrassDividedDepth
