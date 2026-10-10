/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapInjectivity
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedComponents
public import FLT.Mazur.WeierstrassDividedAdjacentZeroComponents

/-!
# Pointwise injectivity of the complete adjacent components

The original parameter pullbacks rule out extra identifications between affine charts.
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
/-- The full first retained component identifies no distinct scheme points. -/
theorem adjacentRetainedFirstComponent_point_injective (hk0 : 0 < start + j) :
    Function.Injective
      (adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr)
    (E) (ProjectiveLine.chartScaling K (tangent)⁻¹)
    (adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr)
    (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr (by omega) hkNext)
  · exact ProjectiveLine.chartScaling_injective _
  · unfold adjacentRetainedFirstParameter adjacentRetainedOldGlobalTensorChart
      adjacentRetainedOldTensorChart adjacentRetainedOldChart
    exact Scheme.Hom.injective _
  · unfold olderGlobalMiddleFirstLine
    exact Scheme.Hom.injective _
  · exact adjacentRetainedFirstComponent_left hπ data D j hj hk0 hk hjNext hkNext r hr
  · exact adjacentRetainedFirstComponent_right hπ data D j hj hk0 hk hjNext hkNext r hr
  · rw [conicZeroAffineIso_puncture, ← ProjectiveLine.scaledReciprocal_overlap]
    exact adjacentRetainedFirstParameter_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr

/-- The full second retained component identifies no distinct scheme points. -/
theorem adjacentRetainedSecondComponent_point_injective (hk0 : 0 < start + j) :
    Function.Injective
      (adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr)
    (E) (ProjectiveLine.chartScaling K (-tangent)⁻¹)
    (adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr)
    (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr (by omega) hkNext)
  · exact ProjectiveLine.chartScaling_injective _
  · unfold adjacentRetainedSecondParameter adjacentRetainedOldGlobalTensorChart
      adjacentRetainedOldTensorChart adjacentRetainedOldChart
    exact Scheme.Hom.injective _
  · unfold olderGlobalMiddleSecondLine
    exact Scheme.Hom.injective _
  · exact adjacentRetainedSecondComponent_left hπ data D j hj hk0 hk hjNext hkNext r hr
  · exact adjacentRetainedSecondComponent_right hπ data D j hj hk0 hk hjNext hkNext r hr
  · rw [conicZeroAffineIso_puncture, ← ProjectiveLine.scaledReciprocal_overlap]
    exact adjacentRetainedSecondParameter_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr

/-- The full first zero component identifies no distinct scheme points. -/
theorem adjacentZeroFirstComponent_point_injective (hk0 : start + j = 0) :
    Function.Injective (adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr)
    (E) (ProjectiveLine.chartScaling K (tangent)⁻¹)
    (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr)
    (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr (by omega) hkNext)
  · exact ProjectiveLine.chartScaling_injective _
  · unfold adjacentZeroFirstParameter adjacentRetainedOldGlobalTensorChart
      adjacentRetainedOldTensorChart adjacentRetainedOldChart
    exact Scheme.Hom.injective _
  · unfold olderGlobalMiddleFirstLine
    exact Scheme.Hom.injective _
  · exact adjacentZeroFirstComponent_left hπ data D j hj hk0 hk hjNext hkNext r hr
  · exact adjacentZeroFirstComponent_right hπ data D j hj hk0 hk hjNext hkNext r hr
  · rw [conicZeroAffineIso_puncture, ← ProjectiveLine.scaledReciprocal_overlap]
    exact adjacentZeroFirstParameter_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr

/-- The full second zero component identifies no distinct scheme points. -/
theorem adjacentZeroSecondComponent_point_injective (hk0 : start + j = 0) :
    Function.Injective (adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) := by
  apply ProjectiveLine.map_injective_of_parameter_pullback
    (adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr)
    (E) (ProjectiveLine.chartScaling K (-tangent)⁻¹)
    (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr)
    (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr (by omega) hkNext)
  · exact ProjectiveLine.chartScaling_injective _
  · unfold adjacentZeroSecondParameter adjacentRetainedOldGlobalTensorChart
      adjacentRetainedOldTensorChart adjacentRetainedOldChart
    exact Scheme.Hom.injective _
  · unfold olderGlobalMiddleSecondLine
    exact Scheme.Hom.injective _
  · exact adjacentZeroSecondComponent_left hπ data D j hj hk0 hk hjNext hkNext r hr
  · exact adjacentZeroSecondComponent_right hπ data D j hj hk0 hk hjNext hkNext r hr
  · rw [conicZeroAffineIso_puncture, ← ProjectiveLine.scaledReciprocal_overlap]
    exact adjacentZeroSecondParameter_isPullback hπ data D j hj hk0 hk hjNext hkNext r hr

end FLT.Mazur.WeierstrassDividedDepth
