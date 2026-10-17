/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentBoundaryCorrectionSplit
public import FLT.Mazur.LaurentScaledEvaluationCoefficients
public import FLT.Mazur.LaurentCoefficientEvaluation
public import FLT.Mazur.PolygonSmoothingRingMap

/-!
# Coefficient naturality of full Laurent correction lifts

Positive and complementary fields, reciprocal coordinates, and the finite
whole-node lifts commute with coefficient maps. Surjective coefficient maps
therefore provide finite Laurent lifts without dropping either tail.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentBoundaryCorrectionSplit
open LaurentPolynomial LaurentBoundaryVectorField PolygonSmoothing
open PolygonScalingNaturality LaurentScaledEvaluationCoefficients LaurentCoefficientEvaluation
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Changing coefficients fixes every integral Laurent monomial. -/
theorem coeffMap_integer (k : ℤ) : coeffMap f (T k) = T k := by
  rw [coeffMap, eval₂_T, coordinate_one_zpow]

/-- The positive part is preserved term by term by coefficient substitution. -/
theorem positivePart_coeffMap (q : R[T;T⁻¹]) :
    positivePart (coeffMap f q) = coeffMap f (positivePart q) := by
  ext k
  rw [positivePart_coeff, coeffMap_coeff, coeffMap_coeff, positivePart_coeff]
  split_ifs <;> simp only [map_zero]

/-- The full nonpositive tail is preserved too. -/
theorem nonpositivePart_coeffMap (q : R[T;T⁻¹]) :
    nonpositivePart (coeffMap f q) = coeffMap f (nonpositivePart q) := by
  rw [nonpositivePart, nonpositivePart, map_sub, positivePart_coeffMap]

/-- Reciprocal vector fields commute with coefficient changes. -/
theorem reciprocalField_coeffMap (q : R[T;T⁻¹]) :
    reciprocalField (coeffMap f q) = coeffMap f (reciprocalField q) := by
  ext k
  rw [reciprocalField_coeff, coeffMap_coeff, coeffMap_coeff, reciprocalField_coeff, map_neg]

/-- Coefficient substitution preserves every finite outgoing node polynomial. -/
theorem outgoingPolynomialLift_ringMap (t : R) (s : S) (hs : f t = s)
    (q : R[T;T⁻¹]) :
    ringMap f t s hs (outgoingPolynomialLift t q) =
      outgoingPolynomialLift s (coeffMap f q) := by
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [outgoingPolynomialLift_add, RingHom.map_add, hp, hq,
      map_add, outgoingPolynomialLift_add]
  | C_mul_T n r =>
    rw [map_mul, coeffMap_C, coeffMap_integer,
      outgoingPolynomialLift_integer, outgoingPolynomialLift_integer]
    split_ifs
    · rw [map_mul, ringMap_scalar, map_pow, ringMap_left]
    · exact map_zero _

/-- The whole-node boundary lift is compatible with every coefficient quotient. -/
theorem boundaryLift_ringMap (t : R) (s : S) (hs : f t = s) (q : R[T;T⁻¹]) :
    ringMap f t s hs (boundaryLift t q) = boundaryLift s (coeffMap f q) := by
  rw [boundaryLift, boundaryLift, outgoingPolynomialLift_ringMap,
    map_mul, coeffMap_integer]

/-- A surjective coefficient map lifts the complete finite Laurent polynomial. -/
theorem coeffMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (coeffMap f) := by
  intro q
  induction q using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', by rw [map_add, hp', hq']⟩
  | C_mul_T n r =>
    obtain ⟨a, ha⟩ := hf r
    exact ⟨C a * T n, by rw [map_mul, coeffMap_C, coeffMap_integer, ha]⟩

end FLT.Mazur.LaurentBoundaryCorrectionSplit
