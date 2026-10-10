/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassDividedTerminalZeroBranchIntersection

/-!
# The scale-one projective lines abutting the terminal node

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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))
local notation "E" => conicZeroAffineIso c hc
local notation "P₁" => terminalZeroConicFirstParameter hπ data D j hj hk0 hk
local notation "P₂" => terminalZeroConicSecondParameter hπ data D j hj hk0 hk
local notation "B₁" => terminalConicFirstBranch hπ data D j hj hk hp
local notation "B₂" => terminalConicSecondBranch hπ data D j hj hk hp

/-- The original first parameter and right terminal branch agree by reciprocal coordinates. -/
theorem terminalZeroFirstComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₁ =
      ProjectiveLine.overlapRight K ≫ B₂ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact (terminalZeroConicFirstParameter_isPullback hπ data D j hj hk0 hk hp).w.symm

/-- The second parameter and left terminal branch retain the opposite orientation. -/
theorem terminalZeroSecondComponent_overlap :
    ProjectiveLine.overlapLeft K ≫ (E).hom ≫ P₂ =
      ProjectiveLine.overlapRight K ≫ B₁ := by
  rw [← Category.assoc, conicZeroAffineIso_puncture]
  exact (terminalZeroConicSecondParameter_isPullback hπ data D j hj hk0 hk hp).w.symm

/-- The first complete normalization component in the actual global residue model. -/
def terminalZeroFirstComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 1) hj :=
  pushout.desc ((E).hom ≫ P₁) B₂ (terminalZeroFirstComponent_overlap hπ data D j hj hk0 hk hp)

/-- The second complete normalization component in the actual global residue model. -/
def terminalZeroSecondComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (j + 1) hj :=
  pushout.desc ((E).hom ≫ P₂) B₁ (terminalZeroSecondComponent_overlap hπ data D j hj hk0 hk hp)

/-- The first component retains the entire original first conic parameter. -/
@[reassoc] theorem terminalZeroFirstComponent_left :
    ProjectiveLine.left K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp = (E).hom ≫ P₁ :=
  pushout.inl_desc _ _ _

/-- The first component retains the entire original right terminal branch. -/
@[reassoc] theorem terminalZeroFirstComponent_right :
    ProjectiveLine.right K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp = B₂ :=
  pushout.inr_desc _ _ _

/-- The second component retains the entire original second conic parameter. -/
@[reassoc] theorem terminalZeroSecondComponent_left :
    ProjectiveLine.left K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp = (E).hom ≫ P₂ :=
  pushout.inl_desc _ _ _

/-- The second component retains the entire original left terminal branch. -/
@[reassoc] theorem terminalZeroSecondComponent_right :
    ProjectiveLine.right K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp = B₁ :=
  pushout.inr_desc _ _ _

/-- Infinity on the first component is the original terminal node. -/
@[reassoc] theorem terminalZeroFirstComponent_infinity :
    ProjectiveLine.infinity K ≫ terminalZeroFirstComponent hπ data D j hj hk0 hk hp =
      terminalConicNodeSection hπ data D j hj hk hp := by
  rw [ProjectiveLine.infinity, Category.assoc, terminalZeroFirstComponent_right]
  exact terminalConicSecondBranch_origin hπ data D j hj hk hp

/-- Infinity on the second component is the same original terminal node. -/
@[reassoc] theorem terminalZeroSecondComponent_infinity :
    ProjectiveLine.infinity K ≫ terminalZeroSecondComponent hπ data D j hj hk0 hk hp =
      terminalConicNodeSection hπ data D j hj hk hp := by
  rw [ProjectiveLine.infinity, Category.assoc, terminalZeroSecondComponent_right]
  exact terminalConicFirstBranch_origin hπ data D j hj hk hp

end FLT.Mazur.WeierstrassDividedDepth
