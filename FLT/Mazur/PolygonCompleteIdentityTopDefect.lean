/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityUnitCoherence
public import FLT.Mazur.PolygonCompleteIdentityOrderZeroLaw
public import FLT.Mazur.PolygonLaurentRestrictionKernel

/-!
# The original top-order multiplication error

If the actual original law holds at order m, its error at order m + 1 lies
in the top square-zero layer. This applies unconditionally to order one.
These assertions retain the actual error and do not assert its vanishing.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "δ" j => completeIdentityFiniteMulDefect K n h i j
local notation "q" => C (C (parameter K (m + 1)))

/-- An established lower-order law places the actual next error in the top parameter power. -/
theorem completeIdentityFiniteMulDefect_top_dvd (hm : (δ m) = 0) :
    (q) ^ (m + 1) ∣ (δ (m + 1)) := by
  apply (doubleLaurent_restriction_eq_zero_iff K m _).mp
  rw [completeIdentityFiniteMulDefect_restriction, hm]

/-- The smoothing parameter kills the next actual error once the lower-order law holds. -/
theorem completeIdentityFiniteMulDefect_top_annihilated (hm : (δ m) = 0) :
    (q) * (δ (m + 1)) = 0 := by
  apply doubleLaurent_parameter_mul_eq_zero K m
  rw [completeIdentityFiniteMulDefect_restriction, hm]

/-- The entire next actual error is square-zero, not just its individual coefficients. -/
theorem completeIdentityFiniteMulDefect_top_sq (hm : (δ m) = 0) :
    (δ (m + 1)) ^ 2 = 0 := by
  apply doubleLaurent_restriction_kernel_sq K m
  rw [completeIdentityFiniteMulDefect_restriction, hm]

/-- At order one, the original error belongs to the top parameter layer unconditionally. -/
theorem completeIdentityFiniteMulDefect_one_top :
    C (C (parameter K 1)) ∣ (δ 1) := by
  simpa only [zero_add, pow_one] using
    completeIdentityFiniteMulDefect_top_dvd K n h i 0
      (completeIdentityFiniteMulDefect_zero K n h i)

/-- At order one the actual error has no products of two infinitesimal corrections. -/
theorem completeIdentityFiniteMulDefect_one_sq : (δ 1) ^ 2 = 0 :=
  completeIdentityFiniteMulDefect_top_sq K n h i 0
    (completeIdentityFiniteMulDefect_zero K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
