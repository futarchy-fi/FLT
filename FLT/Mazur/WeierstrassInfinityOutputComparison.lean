/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityProjectiveOverlap
public import FLT.Mazur.WeierstrassPolynomialOutputComparison

/-!
# Infinity addition versus every polynomial output chart

The cubic difference factor relates the homogeneous infinity law to the
polynomial law. On their concrete intersection it yields an integral output
overlap for every selected polynomial coordinate, not only Y.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Homogeneous factor between polynomial addition and normalized infinity addition. -/
def infinityPolynomialFactor : InfinityAdditionOpen W :=
  infinityOutputRestriction W
    ((infinityRight W (infinitySlopeRestriction W) 0 -
      infinityLeft W (infinitySlopeRestriction W) 0) ^ 3) *
    infinityOutputRestriction W (infinityOutputCoordinates W 1)

/-- The polynomial formula scales the normalized infinity map by the same factor. -/
theorem infinityPolynomial_scaled (i : Fin 3) :
    infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 i) =
      infinityPolynomialFactor W * infinityAdditionChart W (coord W 1 i) := by
  have hs := congrArg (infinityOutputRestriction W)
    (congrFun (infinityOutputCoordinates_scaled W) i)
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul] at hs
  change infinityOutputRestriction W
    (infinitySlopeRestriction W (chartProductAdditionCoordinates W 1 1 i)) = _
  rw [hs, infinityPolynomialFactor]
  have hi := infinityAdditionChart_mul W i
  linear_combination -infinityOutputRestriction W
    ((infinityRight W (infinitySlopeRestriction W) 0 -
      infinityLeft W (infinitySlopeRestriction W) 0) ^ 3) * hi

variable (t : Fin 3)

/-- All polynomial output charts compare to infinity addition on their concrete intersection. -/
theorem infinityProjective_scaled (i : Fin 3) :
    infinityProjectivePolynomial W t
        (additionOutputRestriction W 1 1 t (chartProductAdditionCoordinates W 1 1 i)) =
      infinityProjectiveRestriction W t (infinityPolynomialFactor W) *
        ((infinityProjectiveRestriction W t).comp (infinityAdditionChart W)) (coord W 1 i) := by
  have hs := congrArg (infinityProjectiveRestriction W t) (infinityPolynomial_scaled W i)
  rw [map_mul] at hs
  exact (DFunLike.congr_fun (infinityProjective_inputs W t) _).trans hs

/-- The concrete infinity/polynomial intersection maps into the actual output overlap. -/
def infinityPolynomialOutputLift : Overlap W t 1 →ₐ[R] InfinityProjectiveOverlap W t :=
  polynomialComparisonLift W 1 1 t 1 (infinityProjectivePolynomial W t)
    ((infinityProjectiveRestriction W t).comp (infinityAdditionChart W))
    (infinityProjectiveRestriction W t (infinityPolynomialFactor W))
    (infinityProjective_scaled W t)

/-- Restriction to the selected polynomial chart retains polynomial addition. -/
theorem infinityPolynomialOutputLift_restriction :
    (infinityPolynomialOutputLift W t).comp (overlapRestriction W t 1) =
      (infinityProjectivePolynomial W t).comp (projectiveAdditionChart W 1 1 t) :=
  polynomialComparisonLift_restriction ..

/-- Transition to the Y chart retains the infinity addition law. -/
theorem infinityPolynomialOutputLift_transition :
    (infinityPolynomialOutputLift W t).comp (transitionBase W t 1) =
      (infinityProjectiveRestriction W t).comp (infinityAdditionChart W) :=
  polynomialComparisonLift_transition ..

end FLT.Mazur.WeierstrassIntegralChart
