/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentSplitNodeBranches
public import FLT.Mazur.WeierstrassDividedTerminalSplitNodeBranches
public import FLT.Mazur.WeierstrassDividedFinalBranchChains

/-!
# Positive-depth attachment charts throughout the original chains

Every original first chain chart is its retained conic node branch, including
the final component. The opposite chain keeps its explicit parameter sign.
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

/-- Reindexing retention preserves the first entire node map heterogeneously. -/
theorem olderGlobalResidueFirstNode_retention_heq (j r₁ r₂ : ℕ) (hj : j + 1 ≤ n)
    (hr₁ : j + 1 + r₁ ≤ n) (hr₂ : j + 1 + r₂ ≤ n)
    (hk0 : 0 < start + j) (hdepth : 2 * (start + j + 1) ≤ depth) (h : r₁ = r₂) :
    HEq (olderGlobalResidueFirstNode hπ data D j hj r₁ hr₁ hk0 hdepth)
      (olderGlobalResidueFirstNode hπ data D j hj r₂ hr₂ hk0 hdepth) := by
  subst r₂
  rfl

/-- Reindexing retention likewise preserves the opposite entire node map. -/
theorem olderGlobalResidueSecondNode_retention_heq (j r₁ r₂ : ℕ) (hj : j + 1 ≤ n)
    (hr₁ : j + 1 + r₁ ≤ n) (hr₂ : j + 1 + r₂ ≤ n)
    (hk0 : 0 < start + j) (hdepth : 2 * (start + j + 1) ≤ depth) (h : r₁ = r₂) :
    HEq (olderGlobalResidueSecondNode hπ data D j hj r₁ hr₁ hk0 hdepth)
      (olderGlobalResidueSecondNode hπ data D j hj r₂ hr₂ hk0 hdepth) := by
  subst r₂
  rfl

variable (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
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

/-- Every positive-depth first-chain attachment keeps its original full node branch. -/
@[reassoc] theorem finalBranchComponent_positive_first_left_nodeBranch :
    ProjectiveLine.left K ≫ (finalBranchComponent hπ data D s hs hk hp j 0).left =
      middleNodeFirstBranch c hc ≫ G₁ ≫ transport := by
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h]
    change ProjectiveLine.left K ≫
      finalAdjacentComponent hπ data D s hs hk ⟨j.val, h⟩ 0 = _
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
  · have he : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show j.val = s by omega)
    subst j
    rw [finalBranchComponent_terminal]
    change ProjectiveLine.left K ≫ finalTerminalComponent hπ data D s hs hk hp 0 = _
    rw [finalTerminalComponent_positive hπ data D s hs hk hp hj]
    change ProjectiveLine.left K ≫ terminalFirstComponent hπ data D s hs hj hk hp = _
    rw [terminalFirstComponent_left_nodeBranch]
    apply congrArg (CategoryStruct.comp _)
    apply eq_of_heq
    refine HEq.trans ?_ (comp_eqToHom_heq _ _).symm
    exact olderGlobalResidueFirstNode_retention_heq hπ data D _ _ _ _ _ _ hj _
      (Nat.sub_self s).symm

/-- Every opposite attachment retains the negative original second conic parameter. -/
@[reassoc] theorem finalBranchComponent_positive_second_left_nodeBranch :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ (finalBranchComponent hπ data D s hs hk hp j 1).left =
      middleNodeFirstBranch c hc ≫ G₂ ≫ transport := by
  by_cases h : j.val < s
  · rw [finalBranchComponent, dite_eq_left h]
    change _ ≫ ProjectiveLine.left K ≫
      finalAdjacentComponent hπ data D s hs hk ⟨j.val, h⟩ 1 = _
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
  · have he : j = ⟨s, Nat.lt_succ_self s⟩ := Fin.ext (show j.val = s by omega)
    subst j
    rw [finalBranchComponent_terminal]
    change _ ≫ ProjectiveLine.left K ≫ finalTerminalComponent hπ data D s hs hk hp 1 = _
    rw [finalTerminalComponent_positive hπ data D s hs hk hp hj]
    change _ ≫ ProjectiveLine.left K ≫ terminalSecondComponent hπ data D s hs hj hk hp = _
    rw [terminalSecondComponent_left_nodeBranch]
    apply congrArg (CategoryStruct.comp _)
    apply eq_of_heq
    refine HEq.trans ?_ (comp_eqToHom_heq _ _).symm
    exact olderGlobalResidueSecondNode_retention_heq hπ data D _ _ _ _ _ _ hj _
      (Nat.sub_self s).symm

end FLT.Mazur.WeierstrassDividedDepth
