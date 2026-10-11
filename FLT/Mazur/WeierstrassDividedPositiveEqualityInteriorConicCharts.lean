/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle
public import FLT.Mazur.WeierstrassDividedFinalAdjacentConicBranches

/-!
# Complete earlier conic branches in the positive-start equality cycle

Both original conic restrictions retain their cyclic orientation and the
opposite parameter negation. This includes the first retained pair.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
variable (j : Fin s)
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j.val + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "G₁" => olderGlobalResidueFirstNode hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "G₂" => olderGlobalResidueSecondNode hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)

/-- The incoming cyclic component gives the complete first conic branch. -/
@[reassoc] theorem positiveEqualityCycleComponent_interior_first_conic_chart :
    ProjectiveLine.right K ≫ (Z ⟨j.val + 2, by omega⟩).left =
      middleNodeFirstBranch c hc ≫ G₁ ≫ transport := by
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_first hπ data D s hs hstart hk hp
      ⟨j.val + 1, by omega⟩)
  rw [positiveEqualityBranchComponent_adjacent] at H
  erw [H]
  change ProjectiveLine.right K ≫ ProjectiveLine.endpointReversal K ≫
    finalAdjacentComponent hπ data D s hs hk j 0 = _
  rw [ProjectiveLine.right_endpointReversal_assoc]
  exact finalAdjacentComponent_positive_first_left_nodeBranch hπ data D s hs hk j (by omega)

/-- The outgoing conic branch retains the negative original affine coordinate. -/
@[reassoc] theorem positiveEqualityCycleComponent_interior_second_conic_chart :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left =
      middleNodeFirstBranch c hc ≫ G₂ ≫ transport := by
  have hi : 2 * s + 2 - j.val = 2 * s + 3 - (j.val + 1) := by omega
  have H := congrArg Over.Hom.left
    (positiveEqualityCycleComponent_second hπ data D s hs hstart hk hp
      ⟨j.val + 1, by omega⟩)
  rw [positiveEqualityBranchComponent_adjacent] at H
  have he : (⟨2 * s + 2 - j.val, by omega⟩ : Fin (2 * s + 4)) =
      ⟨2 * s + 3 - (j.val + 1), by omega⟩ := Fin.ext hi
  rw [he]
  erw [H]
  exact finalAdjacentComponent_positive_second_left_nodeBranch hπ data D s hs hk j (by omega)

end FLT.Mazur.WeierstrassDividedDepth
