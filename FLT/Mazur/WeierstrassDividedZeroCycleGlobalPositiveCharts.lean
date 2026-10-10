/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveConicBranches
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveLineBranches
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedZeroCycleGlobalDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps

/-!
# Global descent on the affine charts of positive cyclic components

The conic and horizontal charts retain the reversed first chain and the
negative coordinate of the opposite chain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- The first horizontal chart recovers the original family member. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_positive_first_left (j : Fin s) :
    ProjectiveLine.left K ≫ (Z ⟨j.val + 1, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨j.val + 1, by omega⟩ := by
  rw [zeroSplitCycleComponent_positive_first_lineBranch_assoc,
    zeroSplitCycleGlobalDesc_positive_first, zeroSplitCycleFirstLocalDesc_line]

/-- The opposite horizontal chart retains its negative reciprocal scale. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_positive_second_right (j : Fin s) :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨2 * s + 2 - j.val, by omega⟩ := by
  rw [zeroSplitCycleComponent_positive_second_lineBranch_assoc,
    zeroSplitCycleGlobalDesc_positive_second, zeroSplitCycleSecondLocalDesc_line]

/-- The first conic chart recovers the next cyclic component's right chart. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_positive_first_right (j : Fin s) :
    ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨j.val + 2, by omega⟩ := by
  rw [zeroSplitCycleComponent_positive_first_conicBranch_assoc hπ data D s hs hstart
    (by omega) hp ⟨j.val + 1, by omega⟩ (by dsimp; omega),
    zeroSplitCycleGlobalDesc_positive_first, zeroSplitCycleFirstLocalDesc_conic]

/-- The opposite conic chart recovers its family member with the original tangent sign. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_positive_second_left (j : Fin s) :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 2 - (j.val + 1), by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 2 - (j.val + 1), by omega⟩ := by
  apply middleNode_cancel_chartScaling (-1)
  rw [← middleNode_negativeParameter_eq_scaling]
  rw [zeroSplitCycleComponent_positive_second_conicBranch_assoc hπ data D s hs hstart
    (by omega) hp ⟨j.val + 1, by omega⟩ (by dsimp; omega),
    zeroSplitCycleGlobalDesc_positive_second, zeroSplitCycleSecondLocalDesc_conic]

end FLT.Mazur.WeierstrassDividedDepth
