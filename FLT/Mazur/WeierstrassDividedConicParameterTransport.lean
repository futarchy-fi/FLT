/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentParameterOrigins
public import FLT.Mazur.WeierstrassDividedTerminalParameterOrigins

/-!
# Full conic parameters retain their original chart maps

These comparisons identify the complete parameters, including their origins,
with the original retained conic maps; only stage indices are transported.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
/-- The entire terminal first parameter is the original retained parameter. -/
theorem terminalConicFirstParameter_retained (hk0 : 0 < start + j) :
    terminalConicFirstParameter hπ data D j hj hk0 hk =
      olderGlobalMiddleConicFirstParameter hπ data D j hj 0 hj hk0 hk := by
  unfold terminalConicFirstParameter olderGlobalMiddleConicFirstParameter olderGlobalMiddleConic
  rw [olderGlobalTensorChart_zero_retention]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The entire terminal second parameter is the original retained parameter. -/
theorem terminalConicSecondParameter_retained (hk0 : 0 < start + j) :
    terminalConicSecondParameter hπ data D j hj hk0 hk =
      olderGlobalMiddleConicSecondParameter hπ data D j hj 0 hj hk0 hk := by
  unfold terminalConicSecondParameter olderGlobalMiddleConicSecondParameter
    olderGlobalMiddleConic
  rw [olderGlobalTensorChart_zero_retention]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The entire terminal zero first parameter is the original retained parameter. -/
theorem terminalZeroConicFirstParameter_retained (hk0 : start + j = 0) :
    terminalZeroConicFirstParameter hπ data D j hj hk0 hk =
      olderGlobalZeroConicFirstParameter hπ data D j hj 0 hj hk0 hk := by
  unfold terminalZeroConicFirstParameter olderGlobalZeroConicFirstParameter olderGlobalZeroConic
  unfold olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  rw [olderGlobalTensorChart_zero_retention]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The entire terminal zero second parameter is the original retained parameter. -/
theorem terminalZeroConicSecondParameter_retained (hk0 : start + j = 0) :
    terminalZeroConicSecondParameter hπ data D j hj hk0 hk =
      olderGlobalZeroConicSecondParameter hπ data D j hj 0 hj hk0 hk := by
  unfold terminalZeroConicSecondParameter olderGlobalZeroConicSecondParameter olderGlobalZeroConic
  unfold olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  rw [olderGlobalTensorChart_zero_retention]
  simp only [Category.assoc, WeierstrassCurve.map]

variable (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K
    (a := j + 1 + (r + 1)) (b := j + 2 + r) (by omega) hr (by omega))

/-- The entire adjacent retained first parameter changes only its target index. -/
theorem adjacentRetainedFirstParameter_transport (hk0 : 0 < start + j) :
    adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr =
      olderGlobalMiddleConicFirstParameter hπ data D j hj (r + 1) (by omega) hk0 hk ≫
        transport := by
  unfold adjacentRetainedFirstParameter olderGlobalMiddleConicFirstParameter olderGlobalMiddleConic
  rw [adjacentRetainedOldGlobalTensorChart_transport]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The entire adjacent retained second parameter changes only its target index. -/
theorem adjacentRetainedSecondParameter_transport (hk0 : 0 < start + j) :
    adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr =
      olderGlobalMiddleConicSecondParameter hπ data D j hj (r + 1) (by omega) hk0 hk ≫
        transport := by
  unfold adjacentRetainedSecondParameter olderGlobalMiddleConicSecondParameter
    olderGlobalMiddleConic
  rw [adjacentRetainedOldGlobalTensorChart_transport]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The entire adjacent zero first parameter changes only its target index. -/
theorem adjacentZeroFirstParameter_transport (hk0 : start + j = 0) :
    adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr =
      olderGlobalZeroConicFirstParameter hπ data D j hj (r + 1) (by omega) hk0 hk ≫
        transport := by
  unfold adjacentZeroFirstParameter olderGlobalZeroConicFirstParameter olderGlobalZeroConic
  unfold olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  rw [adjacentRetainedOldGlobalTensorChart_transport]
  simp only [Category.assoc, WeierstrassCurve.map]

/-- The entire adjacent zero second parameter changes only its target index. -/
theorem adjacentZeroSecondParameter_transport (hk0 : start + j = 0) :
    adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr =
      olderGlobalZeroConicSecondParameter hπ data D j hj (r + 1) (by omega) hk0 hk ≫
        transport := by
  unfold adjacentZeroSecondParameter olderGlobalZeroConicSecondParameter olderGlobalZeroConic
  unfold olderGlobalZeroSuccessiveChart zeroResidueConicImmersion
  rw [adjacentRetainedOldGlobalTensorChart_transport]
  simp only [Category.assoc, WeierstrassCurve.map]

end FLT.Mazur.WeierstrassDividedDepth
