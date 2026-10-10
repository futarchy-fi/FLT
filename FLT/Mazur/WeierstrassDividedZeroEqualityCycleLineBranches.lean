/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalParameterLineCharts
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# Horizontal attachments in the original equality-depth cycle

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
  (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 2 + (s - (j.val + 1)) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D (j.val + 1) (by omega)
  (s - (j.val + 1)) (by omega) (by omega) (by omega)

local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The reversed first cyclic chart is the scaled original next horizontal branch. -/
@[reassoc] theorem zeroEqualityCycleComponent_positive_first_lineBranch :
    ProjectiveLine.left K ≫ (Z ⟨j.val + 1, by omega⟩).left =
      ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleParameterLineBranch c ≫ G₁ ≫
        transport := by
  have H := congrArg Over.Hom.left
    (zeroEqualityCycleComponent_first hπ data D s hs hstart hk hp j)
  rw [H]
  change ProjectiveLine.left K ≫ ProjectiveLine.endpointReversal K ≫
    finalAdjacentComponent hπ data D s hs hk j 0 = _
  rw [ProjectiveLine.left_endpointReversal_assoc,
    finalAdjacentComponent_first_right_parameterBranch hπ data D s hs hk j]

/-- The opposite cyclic chart is the negatively scaled original next horizontal branch. -/
@[reassoc] theorem zeroEqualityCycleComponent_positive_second_lineBranch :
    ProjectiveLine.right K ≫ (Z ⟨2 * s + 1 - j.val, by omega⟩).left =
      ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleParameterLineBranch c ≫ G₂ ≫
        transport := by
  have H := congrArg Over.Hom.left
    (zeroEqualityCycleComponent_second hπ data D s hs hstart hk hp j)
  rw [H]
  exact finalAdjacentComponent_second_right_parameterBranch hπ data D s hs hk j

end FLT.Mazur.WeierstrassDividedDepth
