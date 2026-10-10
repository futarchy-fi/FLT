/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceBranch
public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodes
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroConic

/-!
# Original branch maps on the retained start-zero node opens

The localized pushout branches retain the complete original conic parameters
and incidence maps after inclusion into every later global model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)

/-- The first localized conic branch is the complete original retained first parameter. -/
@[reassoc] theorem olderGlobalZeroFirstNode_conicBranch :
    (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫
        olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk =
      olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroFirstNode, fullNodeFirstBranch_firstChart_assoc]
  rfl

/-- The opposite localized conic branch retains the original second parameter. -/
@[reassoc] theorem olderGlobalZeroSecondNode_conicBranch :
    (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫
        olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk =
      olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroSecondNode, fullNodeFirstBranch_secondChart_assoc]
  rfl

/-- The other first-node branch is the original incidence map on its exact principal open. -/
@[reassoc] theorem olderGlobalZeroFirstNode_incidenceBranch :
    fullNodeSecondBranch a c ha ≫
        olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroFirstNode, fullNodeSecondBranch_firstChart_assoc]
  rfl

/-- The opposite incidence branch keeps both its localization and slope translation. -/
@[reassoc] theorem olderGlobalZeroSecondNode_incidenceBranch :
    fullNodeSecondBranch (-a) c (ha).neg ≫
        olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk =
      NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroSecondNode, fullNodeSecondBranch_secondChart_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
