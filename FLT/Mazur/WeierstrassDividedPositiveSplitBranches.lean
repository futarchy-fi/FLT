/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitBranchIndices
public import FLT.Mazur.WeierstrassDividedEqualityInitialEndpoints
public import FLT.Mazur.WeierstrassDividedEqualityInitialExterior

/-!
# Complete original branches at positive start and strict terminal depth

Prepend each original initial projective component to its actual strict branch.
The exterior and both branches retain their complete maps over the residue field.
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
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "N" => finalNodeOverSection hπ data D s hs hk hp
local notation "b" => positiveSplitBranchNode start s hstart

/-- The attachment family embeds as the identical whole sections in the strict node family. -/
theorem finalNodeOverSection_attachment (i : EqualityNodeIndex start s) :
    N (.inl i) = equalityNodeOverSection hπ data D s hs hk i := by
  cases i <;> rfl

/-- The complete initial projective line followed by the complete strict branch. -/
def positiveSplitBranchComponent (j : Fin (s + 2)) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h : j.val = 0 then equalityInitialOverComponent hπ data D s hs hstart hk i
  else finalBranchComponent hπ data D s hs hk hp ⟨j.val - 1, by omega⟩ i

/-- The first edge is precisely the original initial projective component. -/
theorem positiveSplitBranchComponent_initial (i : Fin 2) :
    positiveSplitBranchComponent hπ data D s hs hstart hk hp 0 i =
      equalityInitialOverComponent hπ data D s hs hstart hk i := by
  simp only [positiveSplitBranchComponent, Fin.val_zero, dite_true]

/-- The remaining edges are the actual complete strict branch, in its original order. -/
theorem positiveSplitBranchComponent_tail (j : Fin (s + 1)) (i : Fin 2) :
    positiveSplitBranchComponent hπ data D s hs hstart hk hp ⟨j.val + 1, by omega⟩ i =
      finalBranchComponent hπ data D s hs hk hp j i := by
  rw [positiveSplitBranchComponent, dite_eq_right (show ¬j.val + 1 = 0 by omega)]
  rfl

/-- Each zero is the corresponding original initial or retained node. -/
@[reassoc] theorem positiveSplitBranchComponent_zero (j : Fin (s + 2)) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫
        positiveSplitBranchComponent hπ data D s hs hstart hk hp j i =
      N (b ⟨j.val, by omega⟩ i) := by
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    change _ = N (b 0 i)
    rw [positiveSplitBranchComponent_initial, positiveSplitBranchNode_initial,
      finalNodeOverSection_attachment, equalityInitialOverComponent_zero]
  · let k : Fin (s + 1) := ⟨j.val - 1, by omega⟩
    have he : j = ⟨k.val + 1, by omega⟩ := Fin.ext (by dsimp [k]; omega)
    rw [he, positiveSplitBranchComponent_tail, finalBranchComponent_zero,
      positiveSplitBranchNode_tail start s hstart ⟨k.val, by omega⟩]

/-- Each infinity is the next original vertex, including the common strict terminal node. -/
@[reassoc] theorem positiveSplitBranchComponent_infinity (j : Fin (s + 2)) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        positiveSplitBranchComponent hπ data D s hs hstart hk hp j i =
      N (b ⟨j.val + 1, by omega⟩ i) := by
  rw [positiveSplitBranchNode_tail]
  by_cases hj : j.val = 0
  · have he : j = 0 := Fin.ext hj
    subst j
    rw [positiveSplitBranchComponent_initial, equalityInitialOverComponent_infinity]
    simp only [finalBranchVertex, Fin.val_zero, dite_eq_left (show 0 < s + 1 by omega)]
    rfl
  · rw [positiveSplitBranchComponent, dite_eq_right hj, finalBranchComponent_infinity]
    congr 2
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    omega

/-- The original exterior zero remains the first original initial node. -/
@[reassoc] theorem positiveSplitExterior_zero :
    ProjectiveLine.zeroSection K ≫
        equalityInitialExteriorOverComponent hπ data D s hs hstart hk = N (b 0 0) := by
  rw [positiveSplitBranchNode_initial, finalNodeOverSection_attachment,
    equalityInitialExteriorOverComponent_zero]

/-- The original exterior infinity remains the second original initial node. -/
@[reassoc] theorem positiveSplitExterior_infinity :
    ProjectiveLine.infinitySection K ≫
        equalityInitialExteriorOverComponent hπ data D s hs hstart hk = N (b 0 1) := by
  rw [positiveSplitBranchNode_initial, finalNodeOverSection_attachment,
    equalityInitialExteriorOverComponent_infinity]

end FLT.Mazur.WeierstrassDividedDepth
