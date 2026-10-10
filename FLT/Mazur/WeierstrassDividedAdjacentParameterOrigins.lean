/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedComponents
public import FLT.Mazur.WeierstrassDividedAdjacentZeroComponents
public import FLT.Mazur.WeierstrassDividedFinalNodeFamily
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints

/-!
# Adjacent conic origins retain their original ordered nodes

The full parameter marking is the original retained ordered section, including
scale one. No change of node coordinates or orientation is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))

local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K
    (a := j + 1 + (r + 1)) (b := j + 2 + r) (by omega) hr (by omega))

/-- The adjacent old chart changes only the presentation of its target index. -/
theorem adjacentRetainedOldGlobalTensorChart_transport :
    adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr =
      olderGlobalTensorChart hπ data K j hj (r + 1) (by omega) ≫ transport := by
  apply eq_of_heq
  exact (adjacentRetainedOldGlobalTensorChart_heq hπ data K j hj r hr).symm.trans
    (comp_eqToHom_heq _ _).symm

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hk : 2 * (start + j + 1) ≤ depth)

/-- The first full positive-depth parameter keeps its original retained origin. -/
@[reassoc] theorem adjacentRetainedFirstParameter_origin
    (hk0 : 0 < start + j) :
    o ≫ adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr =
      olderGlobalFirstSection hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentRetainedFirstParameter, Category.assoc,
    conicFirstParameterIso_origin_assoc, adjacentRetainedOldGlobalTensorChart_transport]
  rw [← olderGlobalFirstSection_conic hπ data D j hj (r + 1) (by omega) hk0 hk,
    olderGlobalMiddleConic]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The second full positive-depth parameter keeps its original retained origin. -/
@[reassoc] theorem adjacentRetainedSecondParameter_origin
    (hk0 : 0 < start + j) :
    o ≫ adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr =
      olderGlobalSecondSection hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentRetainedSecondParameter, Category.assoc,
    conicSecondParameterIso_origin_assoc, adjacentRetainedOldGlobalTensorChart_transport]
  rw [← olderGlobalSecondSection_conic hπ data D j hj (r + 1) (by omega) hk0 hk,
    olderGlobalMiddleConic]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The first full scale-one parameter keeps its original retained origin. -/
@[reassoc] theorem adjacentZeroFirstParameter_origin
    (hk0 : start + j = 0) :
    o ≫ adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr =
      olderGlobalZeroFirstSection hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentZeroFirstParameter, Category.assoc,
    conicFirstParameterIso_origin_assoc, adjacentRetainedOldGlobalTensorChart_transport]
  rw [← olderGlobalZeroFirstSection_conic hπ data D j hj (r + 1) (by omega) hk0 hk,
    olderGlobalZeroConic]
  unfold olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The second full scale-one parameter keeps its original retained origin. -/
@[reassoc] theorem adjacentZeroSecondParameter_origin
    (hk0 : start + j = 0) :
    o ≫ adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr =
      olderGlobalZeroSecondSection hπ data D j hj (r + 1) (by omega) hk0 hk ≫ transport := by
  rw [adjacentZeroSecondParameter, Category.assoc,
    conicSecondParameterIso_origin_assoc, adjacentRetainedOldGlobalTensorChart_transport]
  rw [← olderGlobalZeroSecondSection_conic hπ data D j hj (r + 1) (by omega) hk0 hk,
    olderGlobalZeroConic]
  unfold olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  simp only [Category.assoc, WeierstrassCurve.map]

end FLT.Mazur.WeierstrassDividedDepth
