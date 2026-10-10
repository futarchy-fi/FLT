/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassDividedTerminalBranchIntersection

/-!
# The two complete projective lines abutting the terminal node

Glue each original full conic parameter to the opposite full terminal branch
using the already computed Laurent pullback. The first conic uses the right
terminal branch, and the second uses the left terminal branch.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))
local notation "E" => conicZeroAffineIso c hc
local notation "P₁" => terminalConicFirstParameter hπ data D j hj hk0 hk
local notation "P₂" => terminalConicSecondParameter hπ data D j hj hk0 hk
local notation "B₁" => terminalConicFirstBranch hπ data D j hj hk hp
local notation "B₂" => terminalConicSecondBranch hπ data D j hj hk hp

/-- The original first parameter and right terminal branch agree by reciprocal coordinates. -/
theorem terminalFirstComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₁ =
      ProjectiveLine.overlapRight K ≫ B₂ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact (terminalConicFirstParameter_isPullback hπ data D j hj hk0 hk hp).w.symm

/-- The second parameter and left terminal branch retain the opposite orientation. -/
theorem terminalSecondComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₂ =
      ProjectiveLine.overlapRight K ≫ B₁ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact (terminalConicSecondParameter_isPullback hπ data D j hj hk0 hk hp).w.symm

/-- The first complete normalization component in the actual global residue model. -/
def terminalFirstComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 1) hj :=
  pushout.desc ((E).hom ≫ P₁) B₂ (terminalFirstComponent_overlap hπ data D j hj hk0 hk hp)

/-- The second complete normalization component in the actual global residue model. -/
def terminalSecondComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 1) hj :=
  pushout.desc ((E).hom ≫ P₂) B₁ (terminalSecondComponent_overlap hπ data D j hj hk0 hk hp)

/-- The first component retains the entire original first conic parameter. -/
@[reassoc] theorem terminalFirstComponent_left :
    ProjectiveLine.left K ≫ terminalFirstComponent hπ data D j hj hk0 hk hp = (E).hom ≫ P₁ :=
  pushout.inl_desc _ _ _

/-- The first component retains the entire original right terminal branch. -/
@[reassoc] theorem terminalFirstComponent_right :
    ProjectiveLine.right K ≫ terminalFirstComponent hπ data D j hj hk0 hk hp = B₂ :=
  pushout.inr_desc _ _ _

/-- The second component retains the entire original second conic parameter. -/
@[reassoc] theorem terminalSecondComponent_left :
    ProjectiveLine.left K ≫ terminalSecondComponent hπ data D j hj hk0 hk hp = (E).hom ≫ P₂ :=
  pushout.inl_desc _ _ _

/-- The second component retains the entire original left terminal branch. -/
@[reassoc] theorem terminalSecondComponent_right :
    ProjectiveLine.right K ≫ terminalSecondComponent hπ data D j hj hk0 hk hp = B₁ :=
  pushout.inr_desc _ _ _

/-- Infinity on the first component is the original terminal node. -/
@[reassoc] theorem terminalFirstComponent_infinity :
    ProjectiveLine.infinity K ≫ terminalFirstComponent hπ data D j hj hk0 hk hp =
      terminalConicNodeSection hπ data D j hj hk hp := by
  rw [ProjectiveLine.infinity, Category.assoc, terminalFirstComponent_right]
  exact terminalConicSecondBranch_origin hπ data D j hj hk hp

/-- Infinity on the second component is the same original terminal node. -/
@[reassoc] theorem terminalSecondComponent_infinity :
    ProjectiveLine.infinity K ≫ terminalSecondComponent hπ data D j hj hk0 hk hp =
      terminalConicNodeSection hπ data D j hj hk hp := by
  rw [ProjectiveLine.infinity, Category.assoc, terminalSecondComponent_right]
  exact terminalConicFirstBranch_origin hπ data D j hj hk hp

end FLT.Mazur.WeierstrassDividedDepth
