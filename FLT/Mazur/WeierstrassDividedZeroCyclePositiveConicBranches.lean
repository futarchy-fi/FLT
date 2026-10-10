/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalSplitBranchCharts
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# Positive-depth conic attachments in the actual cyclic component family

The cyclic first chain reverses its projective endpoints. Both complete conic
branches are identified as scheme morphisms with their original parameter signs.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
  (j : Fin (s + 1)) (hj : 0 < start + j.val)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j.val + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D j.val (by omega)
  (s - j.val) (by omega) hj (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D j.val (by omega)
  (s - j.val) (by omega) hj (by omega)

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- The reversed first cyclic component keeps the complete original conic node branch. -/
@[reassoc] theorem zeroSplitCycleComponent_positive_first_conicBranch :
    ProjectiveLine.right K ≫ (Z ⟨j.val + 1, by omega⟩).left =
      middleNodeFirstBranch c hc ≫ G₁ ≫ transport := by
  have H := congrArg Over.Hom.left
    (zeroSplitCycleComponent_first hπ data D s hs hstart hk hp j)
  rw [H]
  change ProjectiveLine.right K ≫ ProjectiveLine.endpointReversal K ≫
    (finalBranchComponent hπ data D s hs hk hp j 0).left = _
  rw [ProjectiveLine.right_endpointReversal_assoc,
    finalBranchComponent_positive_first_left_nodeBranch hπ data D s hs hk hp j hj]

/-- The opposite cyclic component retains the negative original conic parameter. -/
@[reassoc] theorem zeroSplitCycleComponent_positive_second_conicBranch :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left =
      middleNodeFirstBranch c hc ≫ G₂ ≫ transport := by
  have H := congrArg Over.Hom.left
    (zeroSplitCycleComponent_second hπ data D s hs hstart hk hp j)
  rw [H]
  exact finalBranchComponent_positive_second_left_nodeBranch hπ data D s hs hk hp j hj

end FLT.Mazur.WeierstrassDividedDepth
