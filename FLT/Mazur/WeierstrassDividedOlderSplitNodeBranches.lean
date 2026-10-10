/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalResidueNodes
public import FLT.Mazur.WeierstrassSuccessiveXResidueSplitBranchCharts

/-!
# Original split branches on every retained positive-depth node

The full local pushout branches retain both original global conic parameters
and horizontal lines. The opposite conic retains its explicit parameter sign.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

local notation "C" => residueSuccessiveConicImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "L" => residueSuccessiveLineImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "W₀" => W.map (residue R)

local notation "G₁" => olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk
local notation "G₂" => olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk

/-- The first conic branch is the entire original retained first parameter. -/
@[reassoc] theorem olderGlobalResidueFirstNode_conicBranch (hc : c = 0) :
    middleNodeFirstBranch c hc ≫ G₁ =
      (conicZeroAffineIso c hc).hom ≫
        olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk := by
  simp only [olderGlobalResidueFirstNode, olderResidueFirstNode, Category.assoc]
  rw [residueMiddleFirstNodeChart_conicBranch_assoc]
  rfl

/-- The opposite conic branch retains the negative of the original second parameter. -/
@[reassoc] theorem olderGlobalResidueSecondNode_conicBranch (hc : c = 0) :
    middleNodeFirstBranch c hc ≫ G₂ =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        (conicZeroAffineIso c hc).hom ≫
          olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk := by
  simp only [olderGlobalResidueSecondNode, olderResidueSecondNode, Category.assoc]
  rw [residueMiddleSecondNodeChart_conicBranch_assoc]
  rfl

/-- The first horizontal branch is the entire original retained first line. -/
@[reassoc] theorem olderGlobalResidueFirstNode_lineBranch (hc : c = 0) :
    middleNodeSecondBranch c hc ≫ G₁ =
      olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk := by
  simp only [olderGlobalResidueFirstNode, olderResidueFirstNode, Category.assoc]
  rw [residueMiddleFirstNodeChart_lineBranch_assoc]
  rfl

/-- The opposite horizontal branch is the entire original retained second line. -/
@[reassoc] theorem olderGlobalResidueSecondNode_lineBranch (hc : c = 0) :
    middleNodeSecondBranch c hc ≫ G₂ =
      olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk := by
  simp only [olderGlobalResidueSecondNode, olderResidueSecondNode, Category.assoc]
  rw [residueMiddleSecondNodeChart_lineBranch_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
