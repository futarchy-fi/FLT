/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalSplitBranchCharts

/-!
# Complete conic branches on earlier adjacent components

An earlier retained conic has zero constant even when the final stage is at
 equality depth. These restrictions require only the strict local index bound.
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
  (D : SplitNodeDepth W π depth)

variable (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
  (j : Fin s) (hj : 0 < start + j.val)
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

/-- Every positive-depth first-chain attachment keeps its original full node branch. -/
@[reassoc] theorem finalAdjacentComponent_positive_first_left_nodeBranch :
    ProjectiveLine.left K ≫ finalAdjacentComponent hπ data D s hs hk j 0 =
      middleNodeFirstBranch c hc ≫ G₁ ≫ transport := by
  rw [finalAdjacentComponent, orderedAdjacentComponent_positive hπ data D
    j.val _ _ _ _ _ _ hj]
  change ProjectiveLine.left K ≫
    adjacentRetainedFirstComponent hπ data D j.val _ hj _ _ _ (s - (j.val + 1)) _ ≫ _ = _
  rw [adjacentRetainedFirstComponent_left_nodeBranch_assoc]
  simp only [eqToHom_trans]
  apply congrArg (CategoryStruct.comp _)
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans (HEq.trans ?_ (comp_eqToHom_heq _ _).symm)
  exact olderGlobalResidueFirstNode_retention_heq hπ data D _ _ _ _ _ _ hj _ (by omega)
/-- Every opposite attachment retains the negative original second conic parameter. -/
@[reassoc] theorem finalAdjacentComponent_positive_second_left_nodeBranch :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ finalAdjacentComponent hπ data D s hs hk j 1 =
      middleNodeFirstBranch c hc ≫ G₂ ≫ transport := by
  rw [finalAdjacentComponent, orderedAdjacentComponent_positive hπ data D
    j.val _ _ _ _ _ _ hj]
  change _ ≫ ProjectiveLine.left K ≫
    adjacentRetainedSecondComponent hπ data D j.val _ hj _ _ _ (s - (j.val + 1)) _ ≫ _ = _
  rw [adjacentRetainedSecondComponent_left_nodeBranch_assoc]
  simp only [eqToHom_trans]
  apply congrArg (CategoryStruct.comp _)
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans (HEq.trans ?_ (comp_eqToHom_heq _ _).symm)
  exact olderGlobalResidueSecondNode_retention_heq hπ data D _ _ _ _ _ _ hj _ (by omega)
end FLT.Mazur.WeierstrassDividedDepth
