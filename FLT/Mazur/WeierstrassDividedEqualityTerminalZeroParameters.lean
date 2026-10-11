/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters
public import FLT.Mazur.WeierstrassDividedOlderZeroNodeBranches

/-!
# Complete terminal parameters at the scale-one attachments

Both full conic parameter opens retain the original initial nodes. The
opposite full-node chart already incorporates its slope translation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) = depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "F" => laurentTerminalProjectiveComponent hπ data D j hj hk hp

/-- The complete first parameter keeps its original scale-one attachment. -/
@[reassoc] theorem equalityTerminalFirstNodeParameter_zero_branch (hk0 : start + j = 0) :
    equalityTerminalFirstNodeParameter data D j hj hk hp ≫ F =
      (fullNodeConicParameterIso a c ha).hom ≫
        fullNodeFirstBranch a c ha ≫
          olderGlobalZeroFirstNode hπ data D j hj 0 hj hk0 hk := by
  rw [equalityTerminalFirstNodeParameter, laurentTerminalProjectiveComponent,
    Category.assoc, Iso.inv_hom_id_assoc,
    olderGlobalZeroFirstNode_conicBranch]
  simp only [laurentConicComponentFirstParameter, Category.assoc,
    laurentTerminalComponentMap_conic]
  rw [laurentTerminalOriginalConic_zero hπ data D j hj hk hk0]
  unfold olderGlobalZeroConicFirstParameter olderGlobalZeroConic
    olderGlobalZeroSuccessiveChart
  rw [olderGlobalTensorChart_zero_retention]
  simp only [zeroResidueConicImmersion, Category.assoc]
  rfl

/-- The complete second parameter keeps its original scale-one attachment. -/
@[reassoc] theorem equalityTerminalSecondNodeParameter_zero_branch (hk0 : start + j = 0) :
    equalityTerminalSecondNodeParameter data D j hj hk hp ≫ F =
      (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫
          olderGlobalZeroSecondNode hπ data D j hj 0 hj hk0 hk := by
  rw [equalityTerminalSecondNodeParameter, laurentTerminalProjectiveComponent,
    Category.assoc, Iso.inv_hom_id_assoc,
    olderGlobalZeroSecondNode_conicBranch]
  simp only [laurentConicComponentSecondParameter, Category.assoc,
    laurentTerminalComponentMap_conic]
  rw [laurentTerminalOriginalConic_zero hπ data D j hj hk hk0]
  unfold olderGlobalZeroConicSecondParameter olderGlobalZeroConic
    olderGlobalZeroSuccessiveChart
  rw [olderGlobalTensorChart_zero_retention]
  simp only [zeroResidueConicImmersion, Category.assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
