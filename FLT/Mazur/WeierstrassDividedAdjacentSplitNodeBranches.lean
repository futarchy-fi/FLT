/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderSplitNodeBranches
public import FLT.Mazur.WeierstrassDividedConicParameterTransport
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedComponents

/-!
# The original positive-depth adjacent components through the node branches

Both complete projective components retain their conic parameter charts and
horizontal charts, including the parameter sign and both reciprocal scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
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
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j + 1 + (r + 1) ≤ n) hr (by omega))

/-- The first adjacent component restricts to the original first conic node branch. -/
@[reassoc] theorem adjacentRetainedFirstComponent_left_nodeBranch :
    ProjectiveLine.left K ≫
        adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      middleNodeFirstBranch c hc ≫
        olderGlobalResidueFirstNode hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentRetainedFirstComponent_left, adjacentRetainedFirstParameter_transport,
    olderGlobalResidueFirstNode_conicBranch_assoc]

/-- The opposite adjacent chart keeps the proved negative original conic parameter. -/
@[reassoc] theorem adjacentRetainedSecondComponent_left_nodeBranch :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫
          adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      middleNodeFirstBranch c hc ≫
        olderGlobalResidueSecondNode hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentRetainedSecondComponent_left, adjacentRetainedSecondParameter_transport,
    olderGlobalResidueSecondNode_conicBranch_assoc]

local notation "eNext" => data (Fin.mk (j + 1 + 1) (Nat.lt_succ_of_le hjNext))
local notation "cNext" => residue R (Data.b6 eNext)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D

/-- The first right chart retains its reciprocal scale on the next node's horizontal branch. -/
@[reassoc] theorem adjacentRetainedFirstComponent_right_nodeBranch (hcNext : cNext = 0) :
    ProjectiveLine.right K ≫
        adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleNodeSecondBranch cNext hcNext ≫
        olderGlobalResidueFirstNode hπ data D (j + 1) hjNext r hr (by omega) hkNext := by
  rw [adjacentRetainedFirstComponent_right, olderGlobalResidueFirstNode_lineBranch]

/-- The opposite right chart retains its negative reciprocal scale on the next node. -/
@[reassoc] theorem adjacentRetainedSecondComponent_right_nodeBranch (hcNext : cNext = 0) :
    ProjectiveLine.right K ≫
        adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleNodeSecondBranch cNext hcNext ≫
        olderGlobalResidueSecondNode hπ data D (j + 1) hjNext r hr (by omega) hkNext := by
  rw [adjacentRetainedSecondComponent_right, olderGlobalResidueSecondNode_lineBranch]

end FLT.Mazur.WeierstrassDividedDepth
