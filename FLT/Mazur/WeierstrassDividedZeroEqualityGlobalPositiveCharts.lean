/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityGlobalNodeRestrictions
public import FLT.Mazur.WeierstrassDividedZeroEqualityConicBranches
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleLineBranches
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterSplitComparison
import all FLT.Mazur.WeierstrassDividedZeroEqualityGlobalNodeRestrictions
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasDescent
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorLocalMaps

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "K" => ResidueField R
local notation "d" => zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w

local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The first horizontal chart recovers the original family member. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_positive_first_left (j : Fin (s - 1)) :
    ProjectiveLine.left K ≫ (Z ⟨j.val + 1, by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨j.val + 1, by omega⟩ := by
  rw [zeroEqualityCycleComponent_positive_first_lineBranch_assoc hπ data D s hs hstart
    hk hp ⟨j.val, by omega⟩,
    zeroEqualityPositiveCycleGlobalDesc_positive_first, middleParameterLineBranch_eq_split _ (by
      apply (residue_eq_zero_iff _).mpr
      exact WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1)
        (by omega) _
        (Data.factor6 _)), zeroEqualityCycleInteriorFirstLocalDesc_line]

/-- The opposite horizontal chart retains its negative reciprocal scale. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_positive_second_right (j : Fin (s - 1)) :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 1 - j.val, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨2 * s + 1 - j.val, by omega⟩ := by
  rw [zeroEqualityCycleComponent_positive_second_lineBranch_assoc hπ data D s hs hstart
    hk hp ⟨j.val, by omega⟩,
    zeroEqualityPositiveCycleGlobalDesc_positive_second, middleParameterLineBranch_eq_split _ (by
      apply (residue_eq_zero_iff _).mpr
      exact WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1)
        (by omega) _
        (Data.factor6 _)), zeroEqualityCycleInteriorSecondLocalDesc_line]

/-- The first conic chart recovers the next cyclic component's right chart. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_positive_first_right (j : Fin (s - 1)) :
    ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left ≫ d =
      ProjectiveLine.right K ≫ F ⟨j.val + 2, by omega⟩ := by
  rw [zeroEqualityCycleComponent_positive_first_conicBranch_assoc hπ data D s hs hstart
    (by omega) hp ⟨j.val + 1, by omega⟩ (by dsimp; omega),
    zeroEqualityPositiveCycleGlobalDesc_positive_first,
    zeroEqualityCycleInteriorFirstLocalDesc_conic]

/-- The opposite conic chart recovers its family member with the original tangent sign. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_positive_second_left (j : Fin (s - 1)) :
    ProjectiveLine.left K ≫ (Z ⟨2 * s + 1 - (j.val + 1), by omega⟩).left ≫ d =
      ProjectiveLine.left K ≫ F ⟨2 * s + 1 - (j.val + 1), by omega⟩ := by
  apply middleNode_cancel_chartScaling (-1)
  rw [← middleNode_negativeParameter_eq_scaling]
  rw [zeroEqualityCycleComponent_positive_second_conicBranch_assoc hπ data D s hs hstart
    (by omega) hp ⟨j.val + 1, by omega⟩ (by dsimp; omega),
    zeroEqualityPositiveCycleGlobalDesc_positive_second,
    zeroEqualityCycleInteriorSecondLocalDesc_conic]

end FLT.Mazur.WeierstrassDividedDepth
