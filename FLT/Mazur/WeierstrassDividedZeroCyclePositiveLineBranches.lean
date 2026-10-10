/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalSplitLineCharts
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# Original horizontal attachments in the actual cyclic component family

The cyclic first chain reverses its projective endpoints. The horizontal
branches retain both signed reciprocal scales at every positive-depth node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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
  (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)

local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- The reversed first cyclic chart is the scaled original next horizontal branch. -/
@[reassoc] theorem zeroSplitCycleComponent_positive_first_lineBranch :
    ProjectiveLine.left K ≫ (Z ⟨j.val + 1, by omega⟩).left =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫ G₁ ≫
        transport := by
  have H := congrArg Over.Hom.left
    (zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨j.val, by omega⟩)
  rw [H]
  change ProjectiveLine.left K ≫ ProjectiveLine.endpointReversal K ≫
    (finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ 0).left = _
  rw [ProjectiveLine.left_endpointReversal_assoc,
    finalBranchComponent_first_right_nodeBranch hπ data D s hs hk hp j]

/-- The opposite cyclic chart is the negatively scaled original next horizontal branch. -/
@[reassoc] theorem zeroSplitCycleComponent_positive_second_lineBranch :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫ G₂ ≫
        transport := by
  have H := congrArg Over.Hom.left
    (zeroSplitCycleComponent_second hπ data D s hs hstart hk hp ⟨j.val, by omega⟩)
  rw [H]
  exact finalBranchComponent_second_right_nodeBranch hπ data D s hs hk hp j

end FLT.Mazur.WeierstrassDividedDepth
