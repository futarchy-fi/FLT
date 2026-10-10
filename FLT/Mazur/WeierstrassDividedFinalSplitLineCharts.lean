/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentSplitNodeBranches
public import FLT.Mazur.WeierstrassDividedFinalBranchChains

/-!
# Original horizontal node branches at the ends of the adjacent chains

The right charts retain the original signed reciprocal scales, including the
initial start-zero components. Only their final target index is transported.
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
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
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

/-- The first adjacent chain ends on the actual next horizontal branch with reciprocal scale. -/
@[reassoc] theorem finalBranchComponent_first_right_nodeBranch :
    ProjectiveLine.right K ≫
        (finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ 0).left =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫ G₁ ≫
        transport := by
  rw [finalBranchComponent_adjacent]
  change ProjectiveLine.right K ≫ finalAdjacentComponent hπ data D s hs hk j 0 = _
  rw [finalAdjacentComponent]
  by_cases h : 0 < start + j.val
  · rw [orderedAdjacentComponent_positive hπ data D j.val _ _ _ _ _ _ h]
    change ProjectiveLine.right K ≫ adjacentRetainedFirstComponent hπ data D
      j.val _ h _ _ _ (s - (j.val + 1)) _ ≫ _ = _
    rw [adjacentRetainedFirstComponent_right_nodeBranch_assoc]
  · rw [orderedAdjacentComponent_zero_depth hπ data D j.val _ _ _ _ _ _ (by omega)]
    change ProjectiveLine.right K ≫ adjacentZeroFirstComponent hπ data D
      j.val _ _ _ _ _ (s - (j.val + 1)) _ ≫ _ = _
    rw [adjacentZeroFirstComponent_right_assoc, olderGlobalResidueFirstNode_lineBranch_assoc]

/-- The opposite chain ends on its actual next horizontal branch with negative reciprocal scale. -/
@[reassoc] theorem finalBranchComponent_second_right_nodeBranch :
    ProjectiveLine.right K ≫
        (finalBranchComponent hπ data D s hs hk hp ⟨j.val, by omega⟩ 1).left =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫ G₂ ≫
        transport := by
  rw [finalBranchComponent_adjacent]
  change ProjectiveLine.right K ≫ finalAdjacentComponent hπ data D s hs hk j 1 = _
  rw [finalAdjacentComponent]
  by_cases h : 0 < start + j.val
  · rw [orderedAdjacentComponent_positive hπ data D j.val _ _ _ _ _ _ h]
    change ProjectiveLine.right K ≫ adjacentRetainedSecondComponent hπ data D
      j.val _ h _ _ _ (s - (j.val + 1)) _ ≫ _ = _
    rw [adjacentRetainedSecondComponent_right_nodeBranch_assoc]
  · rw [orderedAdjacentComponent_zero_depth hπ data D j.val _ _ _ _ _ _ (by omega)]
    change ProjectiveLine.right K ≫ adjacentZeroSecondComponent hπ data D
      j.val _ _ _ _ _ (s - (j.val + 1)) _ ≫ _ = _
    rw [adjacentZeroSecondComponent_right_assoc, olderGlobalResidueSecondNode_lineBranch_assoc]

end FLT.Mazur.WeierstrassDividedDepth
