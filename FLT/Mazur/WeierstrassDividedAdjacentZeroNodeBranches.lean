/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderZeroNodeBranches
public import FLT.Mazur.WeierstrassDividedConicParameterTransport
public import FLT.Mazur.WeierstrassDividedAdjacentZeroComponents

/-!
# The localized node branches are the original adjacent projective charts

The first affine chart of each complete adjacent component factors through
its original signed node open, with only the target stage index transported.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j + 1 + (r + 1) ≤ n) hr (by omega))

/-- The first complete projective component restricts to the actual first node branch. -/
@[reassoc] theorem adjacentZeroFirstComponent_left_nodeBranch :
    ProjectiveLine.left K ≫
        adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      (E).hom ≫ (fullNodeConicParameterIso a c ha).hom ≫
        fullNodeFirstBranch a c ha ≫
        olderGlobalZeroFirstNode hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentZeroFirstComponent_left, adjacentZeroFirstParameter_transport,
    olderGlobalZeroFirstNode_conicBranch_assoc]

/-- The opposite complete component restricts to its original signed node branch. -/
@[reassoc] theorem adjacentZeroSecondComponent_left_nodeBranch :
    ProjectiveLine.left K ≫
        adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr =
      (E).hom ≫ (fullNodeConicParameterIso (-a) c (ha).neg).hom ≫
        fullNodeFirstBranch (-a) c (ha).neg ≫
        olderGlobalZeroSecondNode hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentZeroSecondComponent_left, adjacentZeroSecondParameter_transport,
    olderGlobalZeroSecondNode_conicBranch_assoc]

end FLT.Mazur.WeierstrassDividedDepth
