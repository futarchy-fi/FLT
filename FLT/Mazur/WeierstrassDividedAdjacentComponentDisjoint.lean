/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalComponentIntersection
public import FLT.Mazur.WeierstrassDividedAdjacentComponentRanges
public import FLT.Mazur.WeierstrassDividedAdjacentCrossedIntersection
public import FLT.Mazur.WeierstrassDividedAdjacentZeroCrossedIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalIntersections
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedComponents
public import FLT.Mazur.WeierstrassDividedAdjacentZeroComponents

/-!
# Disjointness of the complete ordered adjacent component pair

The four original affine intersections are empty, so the complete components are disjoint.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "E" => conicZeroAffineIso c hc
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
include hkNext in
/-- The ordered full conic parameters have disjoint images in the common stage. -/
theorem adjacentRetainedParameters_disjoint (hk0 : 0 < start + j) :
    Disjoint (Set.range (adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr))
      (Set.range (adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr)) := by
  unfold adjacentRetainedFirstParameter adjacentRetainedSecondParameter
  apply componentRange_disjoint_postcomp
  · unfold adjacentRetainedOldGlobalTensorChart adjacentRetainedOldTensorChart
      adjacentRetainedOldChart
    exact Scheme.Hom.injective _
  · exact WeierstrassSuccessiveX.conicParameters_disjoint_of_zero
      (W.map (residue R)) c (D.a₁_unit.map (residue R)) hc

/-- The two complete adjacent components of opposite tangent order are disjoint. -/
theorem adjacentRetainedComponents_disjoint (hk0 : 0 < start + j) :
    Disjoint
      (Set.range (adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr))
      (Set.range (adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr)) := by
  rw [adjacentRetainedFirstComponent_range, adjacentRetainedSecondComponent_range]
  apply Set.disjoint_union_left.mpr
  constructor
  · exact Set.disjoint_union_right.mpr
      ⟨adjacentRetainedParameters_disjoint hπ data D j hj hk hkNext r hr hk0,
        adjacentRetainedFirstParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr⟩
  · exact Set.disjoint_union_right.mpr
      ⟨(adjacentRetainedSecondParameter_cross_disjoint hπ data D j hj hk0 hk
          hjNext hkNext r hr).symm,
        olderGlobalMiddleLines_disjoint hπ data D (j + 1) hjNext r hr (by omega) hkNext⟩

include hkNext in
/-- The ordered full conic parameters have disjoint images in the common stage. -/
theorem adjacentZeroParameters_disjoint (hk0 : start + j = 0) :
    Disjoint (Set.range (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr))
      (Set.range (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr)) := by
  unfold adjacentZeroFirstParameter adjacentZeroSecondParameter
  apply componentRange_disjoint_postcomp
  · unfold adjacentRetainedOldGlobalTensorChart adjacentRetainedOldTensorChart
      adjacentRetainedOldChart
    exact Scheme.Hom.injective _
  · exact WeierstrassSuccessiveX.conicParameters_disjoint_of_zero
      (W.map (residue R)) c (D.a₁_unit.map (residue R)) hc

/-- The two complete adjacent components of opposite tangent order are disjoint. -/
theorem adjacentZeroComponents_disjoint (hk0 : start + j = 0) :
    Disjoint
      (Set.range (adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr))
      (Set.range (adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr)) := by
  rw [adjacentZeroFirstComponent_range, adjacentZeroSecondComponent_range]
  apply Set.disjoint_union_left.mpr
  constructor
  · exact Set.disjoint_union_right.mpr
      ⟨adjacentZeroParameters_disjoint hπ data D j hj hk hkNext r hr hk0,
        adjacentZeroFirstParameter_cross_disjoint hπ data D j hj hk0 hk hjNext hkNext r hr⟩
  · exact Set.disjoint_union_right.mpr
      ⟨(adjacentZeroSecondParameter_cross_disjoint hπ data D j hj hk0 hk
          hjNext hkNext r hr).symm,
        olderGlobalMiddleLines_disjoint hπ data D (j + 1) hjNext r hr (by omega) hkNext⟩

end FLT.Mazur.WeierstrassDividedDepth
