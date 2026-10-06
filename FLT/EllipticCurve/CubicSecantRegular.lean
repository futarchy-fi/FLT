/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicSecantProjective
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # The secant denominator is regular over every coefficient ring -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Every horizontal coordinate minus a coefficient is a nonzerodivisor.
The argument uses the free rank-two module over the polynomial ring, and
therefore applies over nonreduced coefficient rings as well. -/
theorem affine_x_sub_mem_nonZeroDivisors (a : R) :
    coord W false 0 - algebraMap R (Ring W false) a ∈ nonZeroDivisors (Ring W false) := by
  let e := affineCoordinateRingEquiv W
  have he :
      e (coord W false 0 - algebraMap R (Ring W false) a) =
        algebraMap (Polynomial R) W.toAffine.CoordinateRing (Polynomial.X - Polynomial.C a) := by
    rw [map_sub, affineCoordinateRingEquiv_coord_zero, AlgEquiv.commutes, map_sub]
    rfl
  have hr := Module.Flat.isSMulRegular_of_isRegular
    (M := W.toAffine.CoordinateRing) (Polynomial.monic_X_sub_C a).isRegular
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  apply e.injective
  have h := congrArg e hx
  rw [map_mul, he, map_zero, ← Algebra.smul_def] at h
  have hh : (Polynomial.X - Polynomial.C a) • e x =
      (Polynomial.X - Polynomial.C a) • (0 : W.toAffine.CoordinateRing) := by
    simpa only [smul_zero] using h
  simpa only [map_zero] using hr hh

/-- The x-difference in the ordinary chart product is always a nonzerodivisor. -/
theorem secantDenominator_mem_nonZeroDivisors :
    secantDenominator W ∈ nonZeroDivisors (AffinePairRing W) := by
  let A := Ring W false
  let E := W.map (algebraMap R A)
  let e := chartBaseChangeEquiv W A false
  have he : e (secantDenominator W) =
      coord E false 0 - algebraMap A (Ring E false) (coord W false 0) := by
    unfold secantDenominator
    rw [map_sub]
    have hl := e.commutes (coord W false 0)
    have hr := chartBaseChangeEquiv_coord W A false 0
    exact congrArg₂ (· - ·) hr hl
  apply mem_nonZeroDivisors_of_injective e.injective
  rw [he]
  exact affine_x_sub_mem_nonZeroDivisors E (coord W false 0)

/-- Restriction to the secant open is injective on functions over any base ring. -/
theorem secantRestriction_injective :
    Function.Injective (algebraMap (AffinePairRing W) (SecantRing W)) :=
  IsLocalization.injective (SecantRing W)
    (Submonoid.powers_le.mpr (secantDenominator_mem_nonZeroDivisors W))

end WeierstrassCurve.CubicCharts
