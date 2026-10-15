/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopDefect
public import FLT.Mazur.PolygonLaurentTopCoefficient

/-!
# The actual reduced polynomial obstruction to the next original law

Extracting the canonical top coefficient from the original multiplication
error produces a double Laurent polynomial over K. Given the preceding law,
its vanishing is equivalent to the next full law. At order one this needs
no hypothesis, since the original order-zero law is already proved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "δ" j => completeIdentityFiniteMulDefect K n h i j

/-- The actual top smoothing coefficient of original multiplication, over the reduced field. -/
def completeIdentityFiniteMulObstruction : K[T;T⁻¹][T;T⁻¹] :=
  doubleLaurentStageCoeff K (m + 1) (m + 1) (δ (m + 1))

/-- Once the preceding law holds, the obstruction reconstructs the entire next original error. -/
theorem completeIdentityFiniteMulDefect_from_obstruction (hm : (δ m) = 0) :
    (δ (m + 1)) = C (C (parameter K (m + 1))) ^ (m + 1) *
      coeffMap (coeffMap (algebraMap K (Ring K (m + 1))))
        (completeIdentityFiniteMulObstruction K n h i m) := by
  apply doubleLaurent_restriction_kernel_top
  rw [completeIdentityFiniteMulDefect_restriction, hm]

/-- The reduced polynomial detects exact next-order equality, not just nilpotence. -/
theorem completeIdentityFiniteMulDefect_succ_iff (hm : (δ m) = 0) :
    (δ (m + 1)) = 0 ↔ completeIdentityFiniteMulObstruction K n h i m = 0 := by
  apply doubleLaurent_restriction_kernel_eq_zero_iff
  rw [completeIdentityFiniteMulDefect_restriction, hm]

/-- The coordinate multiplication law is precisely vanishing of its actual additive error. -/
theorem completeIdentityFiniteLaw_iff_defect :
    universalEdgeScaling (Ring K m) ≫ completeIdentityStageTorus K n h i m =
        completeIdentityFiniteOriginalMul K n h i m ↔ (δ m) = 0 := by
  rw [completeIdentityFiniteLaw_iff_unit, completeIdentityFiniteMulDefect, sub_eq_zero]
  constructor
  · intro hu
    have he := congrArg Units.val hu
    simpa [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit] using he
  · intro he
    apply Units.ext
    simpa [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit] using he

/-- At order one the original law is equivalent to a concrete polynomial equation over K. -/
theorem completeIdentityFiniteLaw_one_iff_obstruction :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
        completeIdentityFiniteOriginalMul K n h i 1 ↔
      completeIdentityFiniteMulObstruction K n h i 0 = 0 := by
  rw [completeIdentityFiniteLaw_iff_defect]
  exact completeIdentityFiniteMulDefect_succ_iff K n h i 0
    (completeIdentityFiniteMulDefect_zero K n h i)

/-- The whole original cubic comparison at order one is detected by this same polynomial. -/
theorem completeIdentityFiniteComparison_one_iff_obstruction :
    completeIdentityFiniteScaling K n h 1 ≫ completePointToIntegralCubic K n h 0 =
        completeIdentityFiniteInput K n h 0 1 ≫ completeIdentityActionTarget K n h 0 ↔
      completeIdentityFiniteMulObstruction K n h 0 0 = 0 := by
  rw [completeIdentityFiniteComparison_iff_laurentLaw,
    completeIdentityFiniteLaw_one_iff_obstruction]

/-- The complete compatible error vanishes exactly when every successive obstruction vanishes. -/
theorem completeIdentityFiniteMulDefect_all_iff_obstructions :
    (∀ j, (δ j) = 0) ↔ ∀ j, completeIdentityFiniteMulObstruction K n h i j = 0 := by
  constructor
  · intro he j
    exact (completeIdentityFiniteMulDefect_succ_iff K n h i j (he j)).mp (he (j + 1))
  · intro he j
    induction j with
    | zero => exact completeIdentityFiniteMulDefect_zero K n h i
    | succ j hj => exact (completeIdentityFiniteMulDefect_succ_iff K n h i j hj).mpr (he j)

end FLT.Mazur.PolygonInfinitesimalStages
