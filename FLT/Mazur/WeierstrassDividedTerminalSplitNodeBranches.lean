/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderSplitNodeBranches
public import FLT.Mazur.WeierstrassDividedConicParameterTransport
public import FLT.Mazur.WeierstrassDividedTerminalComponents

/-!
# Original terminal components at their retained positive-depth attachments

The left charts of both terminal components factor through the actual older
node branches, with the opposite conic parameter sign explicitly retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassSuccessiveX
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

/-- The terminal first component starts at the original first conic node branch. -/
@[reassoc] theorem terminalFirstComponent_left_nodeBranch :
    ProjectiveLine.left K ≫ terminalFirstComponent hπ data D j hj hk0 hk hp =
      middleNodeFirstBranch c hc ≫
        olderGlobalResidueFirstNode hπ data D j hj 0 hj hk0 hk := by
  rw [terminalFirstComponent_left, terminalConicFirstParameter_retained,
    olderGlobalResidueFirstNode_conicBranch]

/-- The terminal opposite component starts with the negative original second parameter. -/
@[reassoc] theorem terminalSecondComponent_left_nodeBranch :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ terminalSecondComponent hπ data D j hj hk0 hk hp =
      middleNodeFirstBranch c hc ≫
        olderGlobalResidueSecondNode hπ data D j hj 0 hj hk0 hk := by
  rw [terminalSecondComponent_left, terminalConicSecondParameter_retained,
    olderGlobalResidueSecondNode_conicBranch]

end FLT.Mazur.WeierstrassDividedDepth
