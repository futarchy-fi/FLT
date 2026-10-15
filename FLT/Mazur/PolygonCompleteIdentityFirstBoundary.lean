/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstLinearization
public import FLT.Mazur.PolygonFirstOrderCoordinateCharts

/-!
# Boundary extension test for the canonical original coordinate change

The universal value of the constructed original-law bijection and its
reciprocal determine two concrete boundary extension problems. Polynomial
extensions fixing both origins force the canonical correction to vanish and
therefore give the first positive-order law in the original coordinates.
The extensions themselves are not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial Polynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonChartScaling PolygonInfinitesimal
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "A" => Ring K 1
local notation "q" => completeIdentityFirstCorrection K n h i
local notation "u" => completeIdentityFirstCoordinateEquiv K n h i (A)[T;T⁻¹]
  (coordinateUnit (1 : (A)ˣ))

/-- The universal original-law correction is precisely the explicit stage coordinate unit. -/
theorem completeIdentityFirstCoordinateEquiv_universal : (u) = firstOrderCoordinateUnit (q) :=
  rfl

/-- Boundary extensions of the actual canonical bijection kill its canonical vector field. -/
theorem completeIdentityFirstCorrection_zero_of_boundary (p r : (A)[X])
    (hp : Polynomial.toLaurent p = (u).val)
    (hr : Polynomial.toLaurent r = invert ((u)⁻¹.val))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) : (q) = 0 := by
  rw [completeIdentityFirstCoordinateEquiv_universal, firstOrderCoordinateUnit_val] at hp
  rw [completeIdentityFirstCoordinateEquiv_universal, firstOrderCoordinateUnit_reciprocal] at hr
  exact firstOrderLaurentCoordinate_boundary_rigid (q) p r hp hr hp0 hr0
    (completeIdentityFirstCorrection_at_one K n h i)

/-- These concrete extensions imply equality of the unchanged original first-order law. -/
theorem completeIdentityFiniteLaw_one_of_boundary (p r : (A)[X])
    (hp : Polynomial.toLaurent p = (u).val)
    (hr : Polynomial.toLaurent r = invert ((u)⁻¹.val))
    (hp0 : p.coeff 0 = 0) (hr0 : r.coeff 0 = 0) :
    universalEdgeScaling (A) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  (completeIdentityFiniteLaw_one_iff_correction K n h i).mpr
    (completeIdentityFirstCorrection_zero_of_boundary K n h i p r hp hr hp0 hr0)

end FLT.Mazur.PolygonInfinitesimalStages
