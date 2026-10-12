/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootFinalBranches
public import FLT.Mazur.WeierstrassCoefficientShearRootFinalInitial
public import FLT.Mazur.WeierstrassDividedPositiveEqualityBranches

/-!
# Independent initial and adjacent pairs in the positive-start branches

Assemble the complete independent initial components followed by all adjacent
components. The original equality-depth branch labels and attachments are retained.
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
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

local notation "N" => equalityNodeOverSection hπ data D s hs hk
local notation "b" => positiveEqualityBranchNode start s hstart

/-- The independent initial pair reconstructs the original complete pair over the field. -/
@[reassoc] theorem coefficientShearRootFinalInitialOverComponent_original (i : Fin 2) :
    coefficientShearRootFinalInitialOverComponent hπ data D s hs hstart hk i ≫ (E).hom =
      equalityInitialOverComponent hπ data D s hs hstart hk i := by
  apply Over.OverMorphism.ext
  exact coefficientShearRootFinalInitialComponent_original hπ data D s hs hstart hk i

/-- The independently glued initial pair followed by every complete adjacent pair. -/
def coefficientShearRootPositiveBranchComponent (j : Fin (s + 1)) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h : j.val = 0 then
    coefficientShearRootFinalInitialOverComponent hπ data D s hs hstart hk i
  else coefficientShearRootFinalAdjacentOverComponent hπ data D s hs hk ⟨j.val - 1, by omega⟩ i

/-- Reconstruction preserves the entire positive branch, including its original initial pair. -/
@[reassoc] theorem coefficientShearRootPositiveBranchComponent_original
    (j : Fin (s + 1)) (i : Fin 2) :
    coefficientShearRootPositiveBranchComponent hπ data D s hs hstart hk j i ≫ (E).hom =
      positiveEqualityBranchComponent hπ data D s hs hstart hk j i := by
  unfold coefficientShearRootPositiveBranchComponent positiveEqualityBranchComponent
  split_ifs
  · exact coefficientShearRootFinalInitialOverComponent_original hπ data D s hs hstart hk i
  · exact coefficientShearRootFinalAdjacentOverComponent_original hπ data D s hs hk _ i

/-- The initial position keeps the independent complete initial component with no index shift. -/
theorem coefficientShearRootPositiveBranchComponent_initial (i : Fin 2) :
    coefficientShearRootPositiveBranchComponent hπ data D s hs hstart hk 0 i =
      coefficientShearRootFinalInitialOverComponent hπ data D s hs hstart hk i := by
  simp only [coefficientShearRootPositiveBranchComponent, Fin.val_zero, dite_true]

/-- Every subsequent level keeps the independent complete adjacent component. -/
theorem coefficientShearRootPositiveBranchComponent_adjacent (j : Fin s) (i : Fin 2) :
    coefficientShearRootPositiveBranchComponent hπ data D s hs hstart hk
        ⟨j.val + 1, by omega⟩ i =
      coefficientShearRootFinalAdjacentOverComponent hπ data D s hs hk j i := by
  rw [coefficientShearRootPositiveBranchComponent,
    dite_eq_right (show ¬j.val + 1 = 0 by omega)]
  rfl

/-- Zero retains the original preceding initial or retained attachment. -/
@[reassoc] theorem coefficientShearRootPositiveBranchComponent_zero
    (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootPositiveBranchComponent hπ data D s hs hstart hk j i =
      N (b ⟨j.val, by omega⟩ i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootPositiveBranchComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, positiveEqualityBranchComponent_zero]

/-- Infinity retains the original next branch attachment, including the final retained pair. -/
@[reassoc] theorem coefficientShearRootPositiveBranchComponent_infinity
    (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootPositiveBranchComponent hπ data D s hs hstart hk j i =
      N (b ⟨j.val + 1, by omega⟩ i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootPositiveBranchComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, positiveEqualityBranchComponent_infinity]

end FLT.Mazur.WeierstrassDividedDepth
