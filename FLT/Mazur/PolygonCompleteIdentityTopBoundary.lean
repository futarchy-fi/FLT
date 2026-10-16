/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopLinearization
public import FLT.Mazur.PolygonTopOrderCoordinateCharts

/-!
# Boundary extension test for every canonical top correction

The universal value of the actual top-weight coordinate bijection and its
reciprocal give two original polynomial boundary tests. Once the preceding
law holds, extensions fixing both origins force the next correction to
vanish, hence give equality in the unchanged original coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial Polynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonChartScaling PolygonInfinitesimal
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "q" => completeIdentityTopCorrection K n h i m
local notation "u" => completeIdentityTopCoordinateEquiv K n h i m (A)[T;T⁻¹]
  (coordinateUnit (1 : (A)ˣ))

/-- The universal original-law correction is precisely the explicit stage coordinate unit. -/
theorem completeIdentityTopCoordinateEquiv_universal : (u) = topOrderCoordinateUnit m (q) := by
  apply Units.ext
  change _ + _ ^ (m + 1) * _ = _ + C (_ ^ (m + 1)) * _
  rw [map_pow]
  rfl

/-- Boundary extensions of the actual canonical bijection kill its canonical vector field. -/
theorem completeIdentityTopCorrection_zero_of_boundary
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) (p r : (A)[X])
    (hp : Polynomial.toLaurent p = (u).val)
    (hr : Polynomial.toLaurent r = invert ((u)⁻¹.val))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) : (q) = 0 := by
  rw [completeIdentityTopCoordinateEquiv_universal, topOrderCoordinateUnit_val] at hp
  rw [completeIdentityTopCoordinateEquiv_universal, topOrderCoordinateUnit_reciprocal] at hr
  exact topOrderLaurentCoordinate_boundary_rigid (m + 1) (q) p r hp hr hp0 hr0
    (completeIdentityTopCorrection_at_one K n h i m hm)

/-- These concrete extensions imply equality of the unchanged original next-order law. -/
theorem completeIdentityFiniteLaw_succ_of_boundary
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) (p r : (A)[X])
    (hp : Polynomial.toLaurent p = (u).val)
    (hr : Polynomial.toLaurent r = invert ((u)⁻¹.val))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) :
    universalEdgeScaling (A) ≫ completeIdentityStageTorus K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i (m + 1) :=
  (completeIdentityFiniteLaw_succ_iff_correction K n h i m hm).mpr
    (completeIdentityTopCorrection_zero_of_boundary K n h i m hm p r hp hr hp0 hr0)

end FLT.Mazur.PolygonInfinitesimalStages
