/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineMapRange
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedComponents
public import FLT.Mazur.WeierstrassDividedAdjacentZeroComponents

/-!
# Entire affine images of adjacent projective components

Both conic parameters and their next full lines survive the projective gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Affine coordinate scaling preserves the whole image of any following map. -/
theorem adjacentChartScaling_range {K : Type u} [Field K] {X : Scheme.{u}} (a : Kˣ)
    (f : ProjectiveLine.chart K ⟶ X) :
    Set.range (ProjectiveLine.chartScaling K a ≫ f) = Set.range f := by
  have h : Function.Surjective (ProjectiveLine.chartScaling K a) := by
    intro x
    refine ⟨ProjectiveLine.chartScaling K a⁻¹ x, ?_⟩
    change (ProjectiveLine.chartScaling K a⁻¹ ≫ ProjectiveLine.chartScaling K a) x = x
    rw [← ProjectiveLine.chartScaling_mul, inv_mul_cancel, ProjectiveLine.chartScaling_one]
    rfl
  exact h.range_comp f

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
/-- The complete first retained component retains both full affine pieces. -/
theorem adjacentRetainedFirstComponent_range (hk0 : 0 < start + j) :
    Set.range (adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) =
      Set.range (adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr) ∪
        Set.range (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) := by
  rw [ProjectiveLine.map_range, adjacentRetainedFirstComponent_left,
    adjacentRetainedFirstComponent_right, adjacentChartScaling_range]
  congr 1
  exact (E).hom.homeomorph.surjective.range_comp
    (adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr)

/-- The complete second retained component retains both full affine pieces. -/
theorem adjacentRetainedSecondComponent_range (hk0 : 0 < start + j) :
    Set.range (adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) =
      Set.range (adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr) ∪
        Set.range (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) := by
  rw [ProjectiveLine.map_range, adjacentRetainedSecondComponent_left,
    adjacentRetainedSecondComponent_right, adjacentChartScaling_range]
  congr 1
  exact (E).hom.homeomorph.surjective.range_comp
    (adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr)

/-- The complete first zero component retains both full affine pieces. -/
theorem adjacentZeroFirstComponent_range (hk0 : start + j = 0) :
    Set.range (adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) =
      Set.range (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr) ∪
        Set.range (olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) := by
  rw [ProjectiveLine.map_range, adjacentZeroFirstComponent_left,
    adjacentZeroFirstComponent_right, adjacentChartScaling_range]
  congr 1
  exact (E).hom.homeomorph.surjective.range_comp
    (adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr)

/-- The complete second zero component retains both full affine pieces. -/
theorem adjacentZeroSecondComponent_range (hk0 : start + j = 0) :
    Set.range (adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) =
      Set.range (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr) ∪
        Set.range (olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext r hr
          (by omega) hkNext) := by
  rw [ProjectiveLine.map_range, adjacentZeroSecondComponent_left,
    adjacentZeroSecondComponent_right, adjacentChartScaling_range]
  congr 1
  exact (E).hom.homeomorph.surjective.range_comp
    (adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr)

end FLT.Mazur.WeierstrassDividedDepth
