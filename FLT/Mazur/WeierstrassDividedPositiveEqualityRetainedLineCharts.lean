/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle
public import FLT.Mazur.WeierstrassDividedFinalParameterLineCharts
public import FLT.Mazur.WeierstrassDividedFinalInitialLineCharts

/-!
# Complete horizontal branches in positive-start cyclic coordinates

The first retained pair uses the initial projective components. Every later
pair uses the preceding adjacent components, with both reciprocal scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
variable (j : ℕ) (hj : j ≤ s)
local notation "e" => data (Fin.mk (j + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "t" => WeierstrassDilatation.residueTangentUnit D
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j + 1 + (s - j) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D j (by omega)
  (s - j) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D j (by omega)
  (s - j) (by omega) (by omega) (by omega)

/-- The preceding first-chain component gives the entire horizontal branch. -/
@[reassoc] theorem positiveEqualityCycleComponent_retained_first_line_chart :
    ProjectiveLine.left K ≫ (Z ⟨j + 1, by omega⟩).left =
      ProjectiveLine.chartScaling K (t)⁻¹ ≫ middleParameterLineBranch c ≫ G₁ ≫ transport := by
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_first hπ data D s hs hstart hk hp ⟨j, by omega⟩)
  erw [H]
  change ProjectiveLine.left K ≫ ProjectiveLine.endpointReversal K ≫
    (positiveEqualityBranchComponent hπ data D s hs hstart hk ⟨j, by omega⟩ 0).left = _
  rw [ProjectiveLine.left_endpointReversal_assoc]
  cases j with
  | zero =>
    erw [positiveEqualityBranchComponent_initial]
    exact finalInitialComponent_first_right_parameterBranch hπ data D s hs hstart hk
  | succ j =>
    rw [positiveEqualityBranchComponent_adjacent hπ data D s hs hstart hk ⟨j, by omega⟩]
    exact finalAdjacentComponent_first_right_parameterBranch hπ data D s hs hk ⟨j, by omega⟩

/-- The opposite preceding component keeps its negatively scaled horizontal branch. -/
@[reassoc] theorem positiveEqualityCycleComponent_retained_second_line_chart :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 3 - j, by omega⟩).left =
      ProjectiveLine.chartScaling K (-t)⁻¹ ≫ middleParameterLineBranch c ≫ G₂ ≫ transport := by
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_second hπ data D s hs hstart hk hp ⟨j, by omega⟩)
  erw [H]
  cases j with
  | zero =>
    erw [positiveEqualityBranchComponent_initial]
    exact finalInitialComponent_second_right_parameterBranch hπ data D s hs hstart hk
  | succ j =>
    rw [positiveEqualityBranchComponent_adjacent hπ data D s hs hstart hk ⟨j, by omega⟩]
    exact finalAdjacentComponent_second_right_parameterBranch hπ data D s hs hk ⟨j, by omega⟩

end FLT.Mazur.WeierstrassDividedDepth
