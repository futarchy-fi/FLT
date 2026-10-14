/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootFinalBranches
public import FLT.Mazur.WeierstrassCoefficientShearRootPositiveBranches
public import FLT.Mazur.WeierstrassDividedPositiveSplitBranches

/-!
# Independent initial and adjacent pairs in the positive-start branches

Assemble the complete independent initial components followed by all adjacent
components. The original strict-depth branch labels and the common terminal node are retained.
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
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

local notation "N" => finalNodeOverSection hπ data D s hs hk hp
local notation "b" => positiveSplitBranchNode start s hstart

/-- The independently glued initial pair followed by every complete adjacent pair. -/
def coefficientShearRootStrictPositiveBranchComponent (j : Fin (s + 2)) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h : j.val = 0 then
    coefficientShearRootFinalInitialOverComponent hπ data D s hs hstart hk i
  else coefficientShearRootFinalBranchComponent hπ data D s hs hk hp ⟨j.val - 1, by omega⟩ i

/-- Reconstruction preserves the entire positive branch, including its original initial pair. -/
@[reassoc] theorem coefficientShearRootStrictPositiveBranchComponent_original
    (j : Fin (s + 2)) (i : Fin 2) :
    coefficientShearRootStrictPositiveBranchComponent hπ data D s hs hstart hk hp j i ≫ (E).hom =
      positiveSplitBranchComponent hπ data D s hs hstart hk hp j i := by
  unfold coefficientShearRootStrictPositiveBranchComponent positiveSplitBranchComponent
  split_ifs
  · exact coefficientShearRootFinalInitialOverComponent_original hπ data D s hs hstart hk i
  · exact coefficientShearRootFinalBranchComponent_original hπ data D s hs hk hp _ i

/-- The initial position keeps the independent complete initial component with no index shift. -/
theorem coefficientShearRootStrictPositiveBranchComponent_initial (i : Fin 2) :
    coefficientShearRootStrictPositiveBranchComponent hπ data D s hs hstart hk hp 0 i =
      coefficientShearRootFinalInitialOverComponent hπ data D s hs hstart hk i := by
  simp only [coefficientShearRootStrictPositiveBranchComponent, Fin.val_zero, dite_true]

/-- Every subsequent level keeps its independent adjacent or terminal component. -/
theorem coefficientShearRootStrictPositiveBranchComponent_tail (j : Fin (s + 1)) (i : Fin 2) :
    coefficientShearRootStrictPositiveBranchComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩ i =
      coefficientShearRootFinalBranchComponent hπ data D s hs hk hp j i := by
  rw [coefficientShearRootStrictPositiveBranchComponent,
    dite_eq_right (show ¬j.val + 1 = 0 by omega)]
  rfl

/-- Zero retains the original preceding initial or retained attachment. -/
@[reassoc] theorem coefficientShearRootStrictPositiveBranchComponent_zero
    (j : Fin (s + 2)) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootStrictPositiveBranchComponent hπ data D s hs hstart hk hp j i =
      N (b ⟨j.val, by omega⟩ i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootStrictPositiveBranchComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, positiveSplitBranchComponent_zero]

/-- Infinity retains the original next branch attachment, including the final retained pair. -/
@[reassoc] theorem coefficientShearRootStrictPositiveBranchComponent_infinity
    (j : Fin (s + 2)) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootStrictPositiveBranchComponent hπ data D s hs hstart hk hp j i =
      N (b ⟨j.val + 1, by omega⟩ i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootStrictPositiveBranchComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, positiveSplitBranchComponent_infinity]

end FLT.Mazur.WeierstrassDividedDepth
