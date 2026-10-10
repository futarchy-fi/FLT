/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderZeroNodeBranches
public import FLT.Mazur.WeierstrassDividedZeroExteriorOriented

/-!
# The exterior component on both original localized node branches

The branch maps keep the projective slope normalization and the opposite
chart's translation. Their sources are the actual principal opens.
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
local notation "u" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "E" => zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk

/-- The whole affine incidence chart keeps its coordinates in the oriented exterior. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_incidence :
    ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ E =
      olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedOrientedToGlobal_eq, Iso.hom_inv_id_assoc,
    zeroRetainedProjectiveToGlobal_affine]

/-- The first exact node branch is the corresponding open of the oriented exterior. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_first_nodeBranch :
    NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ E =
      fullNodeSecondBranch a c ha ≫
        olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedOrientedToGlobal_incidence, olderGlobalZeroFirstNode_incidenceBranch]

/-- The opposite exact branch retains the translated slope before projective normalization. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_second_nodeBranch :
    NodeLocalDescent.branchOpen K
        (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
        Spec.map (CommRingCat.ofHom (aeval (X - C a)).toRingHom) ≫
        ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso u).hom ≫ E =
      fullNodeSecondBranch (-a) c (ha).neg ≫
        olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedOrientedToGlobal_incidence, olderGlobalZeroSecondNode_incidenceBranch]

end FLT.Mazur.WeierstrassDividedDepth
