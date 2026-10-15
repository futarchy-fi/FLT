/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField
public import FLT.Mazur.PolygonFirstNodeBoundary
public import FLT.Mazur.PolygonSmoothingReciprocalScaling

/-!
# Boundary polynomials for node maps reducing to original scaling

Normalize an actual node map by its inverse input scaling. Its reduction is
the identity, so the node equation produces a polynomial boundary fixing the
origin. Multiplying this polynomial by the original scale recovers the full
original map, not a replacement action or a reduced-only comparison.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentBoundaryVectorField
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
variable (a : (Ring R 1)ˣ)
  (f : ChartRing (parameter R 1) →ₐ[Ring R 1] ChartRing (parameter R 1))
  (hf : ∀ z, firstNodeReduction R (f z) =
    firstNodeReduction R (reciprocalScale (parameter R 1) a z))

/-- Remove only the prescribed original scaling from the input of the actual node map. -/
def firstNodeScaleNormalize : (B) →ₐ[S] (B) := f.comp (reciprocalScale (e) a⁻¹)

include hf in
/-- Normalization reduces to the identity on every original node function. -/
theorem firstNodeScaleNormalize_reduction (z : B) :
    firstNodeReduction R (firstNodeScaleNormalize R a f z) = firstNodeReduction R z := by
  change firstNodeReduction R (f (reciprocalScale (e) a⁻¹ z)) = _
  rw [hf]
  change firstNodeReduction R
    (((reciprocalScale (e) a).comp (reciprocalScale (e) a⁻¹)) z) = _
  rw [← reciprocalScale_mul, mul_inv_cancel, reciprocalScale_one]
  rfl

/-- The original left coordinate is recovered by multiplying back the specified scale. -/
theorem firstNodeScaleNormalize_left :
    algebraMap (S) (B) a * firstNodeScaleNormalize R a f (leftCoordinate (e)) =
      f (leftCoordinate (e)) := by
  change algebraMap (S) (B) a * f (reciprocalScale (e) a⁻¹ (leftCoordinate (e))) = _
  rw [reciprocalScale_left, map_mul, AlgHom.commutes, ← mul_assoc, ← map_mul,
    Units.mul_inv, map_one, one_mul]

/-- The full boundary polynomial of the original scaling-reducing node map. -/
def firstNodeScaledBoundaryPolynomial : (S)[X] :=
  Polynomial.C a.val * firstNodeBoundaryPolynomial R (firstNodeScaleNormalize R a f)
    (firstNodeScaleNormalize_reduction R a f hf)

/-- The node relation forces the original, unnormalized boundary origin to be fixed. -/
theorem firstNodeScaledBoundaryPolynomial_coeff_zero :
    (firstNodeScaledBoundaryPolynomial R a f hf).coeff 0 = 0 := by
  rw [firstNodeScaledBoundaryPolynomial, Polynomial.coeff_C_mul,
    firstNodeBoundaryPolynomial_coeff_zero, mul_zero]

/-- The constructed polynomial restricts to the full original node map. -/
theorem firstNodeScaledBoundaryPolynomial_toLaurent :
    (firstNodeScaledBoundaryPolynomial R a f hf).toLaurent =
      leftLaurentMap (e) (f (leftCoordinate (e))) := by
  rw [firstNodeScaledBoundaryPolynomial, map_mul, Polynomial.toLaurent_C,
    firstNodeBoundaryPolynomial_toLaurent]
  have he := congrArg (leftLaurentMap (e)) (firstNodeScaleNormalize_left R a f)
  rw [map_mul, AlgHom.commutes] at he
  exact he

include hf in
/-- Every nonpositive Laurent coefficient of the original node restriction vanishes. -/
theorem firstNodeScaledBoundary_coeff_nonpos (d : ℤ) (hd : d ≤ 0) :
    (leftLaurentMap (e) (f (leftCoordinate (e)))).coeff d = 0 := by
  rw [← firstNodeScaledBoundaryPolynomial_toLaurent R a f hf]
  rcases lt_or_eq_of_le hd with hd | rfl
  · exact polynomial_coeff_neg _ d hd
  · rw [polynomial_coeff_zero, firstNodeScaledBoundaryPolynomial_coeff_zero]

end FLT.Mazur.PolygonInfinitesimalStages
