/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroOrderedConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureInclusion

public import FLT.Mazur.WeierstrassDividedAdjacentZeroParameterIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroConic

/-!
# Initial adjacent conic maps retain the original global components

The common adjacent stage changes only the parenthesization of its index.
The original conic and its two parameter maps are preserved heterogeneously.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
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
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)


open WeierstrassModificationX
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr

local notation "P₁" => Iso.inv (conicFirstParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicFirstOpenImmersion (WeierstrassCurve.a₁ W₀) c
local notation "P₂" => Iso.inv (conicSecondParameterIso (WeierstrassCurve.a₁ W₀) c ha) ≫
  conicSecondOpenImmersion (WeierstrassCurve.a₁ W₀) c

/-- The complete initial conic in the common adjacent global stage. -/
def adjacentZeroConic := C ≫ g

/-- The original full conic is unchanged by stage reassociation. -/
theorem adjacentZeroConic_original :
    HEq (olderGlobalZeroConic hπ data D j hj (r + 1) (by omega) hk0 hk)
      (adjacentZeroConic hπ data D j hj hk0 hk r hr) := by
  unfold olderGlobalZeroConic olderGlobalZeroSuccessiveChart adjacentZeroConic
    zeroResidueConicImmersion
  rw [← Category.assoc]
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentRetainedOldGlobalTensorChart_heq hπ data K j hj r hr)

/-- The first original complete parameter remains the same map and source. -/
theorem adjacentZeroFirstParameter_original :
    HEq (olderGlobalZeroConicFirstParameter hπ data D j hj (r + 1) (by omega) hk0 hk)
      (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr) := by
  unfold olderGlobalZeroConicFirstParameter adjacentZeroFirstParameter
  rw [← Category.assoc]
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentZeroConic_original hπ data D j hj hk0 hk r hr)

/-- The second original complete parameter remains the same map and source. -/
theorem adjacentZeroSecondParameter_original :
    HEq (olderGlobalZeroConicSecondParameter hπ data D j hj (r + 1) (by omega) hk0 hk)
      (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr) := by
  unfold olderGlobalZeroConicSecondParameter adjacentZeroSecondParameter
  rw [← Category.assoc]
  exact heq_comp rfl rfl
    (finiteGlobalTensorModel_index_congr hπ data K (by omega) hr (by omega)) HEq.rfl
    (adjacentZeroConic_original hπ data D j hj hk0 hk r hr)

end FLT.Mazur.WeierstrassDividedDepth
