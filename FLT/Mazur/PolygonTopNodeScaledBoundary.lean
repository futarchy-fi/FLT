/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField
public import FLT.Mazur.PolygonTopNodeBoundary
public import FLT.Mazur.PolygonSmoothingReciprocalScaling
public import FLT.Mazur.PolygonTopOrderCoordinateCharts
public import FLT.Mazur.LaurentPositivePart

/-!
# Boundary polynomials for node maps restricting to original scaling

Normalize an actual node map by its inverse input scaling. Its preceding-stage restriction is
the identity, so the node equation produces a polynomial boundary fixing the
origin. Multiplying this polynomial by the original scale recovers the full
original map, not a replacement action or a reduced-only comparison.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentBoundaryVectorField LaurentPositivePart
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
variable (a : (Ring R (m + 1))ˣ)
  (f : ChartRing (parameter R (m + 1)) →ₐ[Ring R (m + 1)] ChartRing (parameter R (m + 1)))
  (hf : ∀ z, topNodeRestriction R m (f z) =
    topNodeRestriction R m (reciprocalScale (parameter R (m + 1)) a z))

/-- Remove only the prescribed original scaling from the input of the actual node map. -/
def topNodeScaleNormalize : (B) →ₐ[S] (B) := f.comp (reciprocalScale (e) a⁻¹)

include hf in
/-- Normalization reduces to the identity on every original node function. -/
theorem topNodeScaleNormalize_reduction (z : B) :
    topNodeRestriction R m (topNodeScaleNormalize R m a f z) = topNodeRestriction R m z := by
  change topNodeRestriction R m (f (reciprocalScale (e) a⁻¹ z)) = _
  rw [hf]
  change topNodeRestriction R m
    (((reciprocalScale (e) a).comp (reciprocalScale (e) a⁻¹)) z) = _
  rw [← reciprocalScale_mul, mul_inv_cancel, reciprocalScale_one]
  rfl

/-- The original left coordinate is recovered by multiplying back the specified scale. -/
theorem topNodeScaleNormalize_left :
    algebraMap (S) (B) a * topNodeScaleNormalize R m a f (leftCoordinate (e)) =
      f (leftCoordinate (e)) := by
  change algebraMap (S) (B) a * f (reciprocalScale (e) a⁻¹ (leftCoordinate (e))) = _
  rw [reciprocalScale_left, map_mul, AlgHom.commutes, ← mul_assoc, ← map_mul,
    Units.mul_inv, map_one, one_mul]

/-- The full boundary polynomial of the original scaling-reducing node map. -/
def topNodeScaledBoundaryPolynomial : (S)[X] :=
  Polynomial.C a.val * topNodeBoundaryPolynomial R m (topNodeScaleNormalize R m a f)
    (topNodeScaleNormalize_reduction R m a f hf)

/-- The node relation forces the original, unnormalized boundary origin to be fixed. -/
theorem topNodeScaledBoundaryPolynomial_coeff_zero :
    (topNodeScaledBoundaryPolynomial R m a f hf).coeff 0 = 0 := by
  rw [topNodeScaledBoundaryPolynomial, Polynomial.coeff_C_mul,
    topNodeBoundaryPolynomial_coeff_zero, mul_zero]

/-- The constructed polynomial restricts to the full original node map. -/
theorem topNodeScaledBoundaryPolynomial_toLaurent :
    (topNodeScaledBoundaryPolynomial R m a f hf).toLaurent =
      leftLaurentMap (e) (f (leftCoordinate (e))) := by
  rw [topNodeScaledBoundaryPolynomial, map_mul, Polynomial.toLaurent_C,
    topNodeBoundaryPolynomial_toLaurent]
  have he := congrArg (leftLaurentMap (e)) (topNodeScaleNormalize_left R m a f)
  rw [map_mul, AlgHom.commutes] at he
  exact he

include hf in
/-- Every nonpositive Laurent coefficient of the original node restriction vanishes. -/
theorem topNodeScaledBoundary_coeff_nonpos (d : ℤ) (hd : d ≤ 0) :
    (leftLaurentMap (e) (f (leftCoordinate (e)))).coeff d = 0 := by
  rw [← topNodeScaledBoundaryPolynomial_toLaurent R m a f hf]
  rcases lt_or_eq_of_le hd with hd | rfl
  · exact polynomial_coeff_neg _ d hd
  · rw [polynomial_coeff_zero, topNodeScaledBoundaryPolynomial_coeff_zero]

include hf in
/-- An original scaling extension kills the full nonpositive top-weight error tail. -/
theorem topNodeScaledExtension_boundaryTail_zero (q : R[T;T⁻¹])
    (hx : leftLaurentMap (e) (f (leftCoordinate (e))) =
      LaurentPolynomial.C a.val * (topOrderCoordinateUnit m q).val) : boundaryTail q = 0 := by
  have he := congrArg (leftLaurentMap (e)) (topNodeScaleNormalize_left R m a f)
  rw [map_mul, AlgHom.commutes, hx] at he
  have hn :=
    (Units.map (LaurentPolynomial.C : (S) →+* (S)[T;T⁻¹]).toMonoidHom a).isUnit.mul_left_cancel he
  rw [topOrderCoordinateUnit_val] at hn
  apply (boundaryTail_eq_zero_iff q).mpr
  intro d hd
  exact topOrderLaurentCoordinate_boundary_coeff (m + 1) q
    (topNodeBoundaryPolynomial R m (topNodeScaleNormalize R m a f)
      (topNodeScaleNormalize_reduction R m a f hf))
    ((topNodeBoundaryPolynomial_toLaurent R m _ _).trans hn)
    (topNodeBoundaryPolynomial_coeff_zero R m _ _) d hd

end FLT.Mazur.PolygonInfinitesimalStages
