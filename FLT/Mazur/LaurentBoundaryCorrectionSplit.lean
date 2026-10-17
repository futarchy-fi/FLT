/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentBoundaryVectorField
public import FLT.Mazur.PolygonSmoothingComplementaryCoefficients

/-!
# Splitting a full Laurent correction between adjacent boundary charts

The positive exponents belong to one boundary chart. In the reciprocal
coordinate, every remaining exponent becomes strictly positive too. Both
pieces have explicit lifts in full smoothing rings; no Laurent term is lost.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentBoundaryCorrectionSplit
open LaurentPolynomial LaurentBoundaryVectorField PolygonSmoothing
variable {R : Type*} [CommRing R]
local notation "L" => R[T;T⁻¹]

/-- Retain precisely the strictly positive Laurent terms. -/
def positivePart (q : L) : L := .ofCoeff (q.coeff.filter fun k ↦ 0 < k)

/-- The full complementary part, including the constant term. -/
def nonpositivePart (q : L) : L := q - positivePart q

/-- The splitting preserves each positive coefficient exactly. -/
theorem positivePart_coeff (q : L) (k : ℤ) :
    (positivePart q).coeff k = if 0 < k then q.coeff k else 0 :=
  Finsupp.filter_apply _ _ _

/-- The complementary part preserves exactly the nonpositive coefficients. -/
theorem nonpositivePart_coeff (q : L) (k : ℤ) :
    (nonpositivePart q).coeff k = if k ≤ 0 then q.coeff k else 0 := by
  simp only [nonpositivePart, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    positivePart_coeff]
  (split_ifs <;> simp_all); omega

/-- All original coefficients, including both tails, are retained in the splitting. -/
theorem parts_add (q : L) : positivePart q + nonpositivePart q = q := by
  unfold nonpositivePart
  abel

/-- Changing to the reciprocal vector field twice recovers the original field. -/
theorem reciprocalField_involutive (q : L) : reciprocalField (reciprocalField q) = q := by
  ext k
  rw [reciprocalField_coeff, reciprocalField_coeff, neg_neg]
  congr 1
  omega

/-- The complementary correction vanishes at the reciprocal boundary origin. -/
theorem reciprocal_nonpositive_coeff (q : L) (k : ℤ) (hk : k ≤ 0) :
    (reciprocalField (nonpositivePart q)).coeff k = 0 := by
  rw [reciprocalField_coeff, nonpositivePart_coeff, ite_eq_right (by omega), neg_zero]

/-- Multiplying by a Laurent power shifts every coefficient with no discarded tail. -/
theorem shifted_coeff (q : L) (a k : ℤ) : (T a * q).coeff k = q.coeff (k - a) := by
  change (AddMonoidAlgebra.single a 1 * q).coeff k = _
  rw [AddMonoidAlgebra.coeff_single_mul_apply]
  simp only [one_mul]
  congr 1
  omega

/-- A nonnegative Laurent polynomial is the exact outgoing value of its finite node lift. -/
theorem outgoingLift_eq (t : R) (q : L) (hq : ∀ k : ℤ, k < 0 → q.coeff k = 0) :
    leftLaurentMap t (outgoingPolynomialLift t q) = q := by
  ext k
  rw [outgoingPolynomialLift_left_coeff]
  split_ifs with hk
  · rfl
  · exact (hq k (by omega)).symm

/-- A vector field vanishing at its boundary is a coordinate times a full node function. -/
def boundaryLift (t : R) (q : L) : ChartRing t := outgoingPolynomialLift t (T (-1) * q)

/-- The lifted function realizes the entire specified vector field on the puncture. -/
theorem boundaryLift_value (t : R) (q : L) (hq : ∀ k : ℤ, k ≤ 0 → q.coeff k = 0) :
    T 1 * leftLaurentMap t (boundaryLift t q) = q := by
  rw [boundaryLift, outgoingLift_eq t _ (by
    intro k hk
    rw [shifted_coeff]
    exact hq _ (by omega))]
  rw [← mul_assoc, ← T_add]
  norm_num

/-- The positive correction has a full node lift for any smoothing parameter. -/
theorem positivePart_lift (t : R) (q : L) :
    T 1 * leftLaurentMap t (boundaryLift t (positivePart q)) = positivePart q :=
  boundaryLift_value t _ (fun k hk ↦ by rw [positivePart_coeff, ite_eq_right (by omega)])

/-- The entire complementary correction has a full lift in the reciprocal chart. -/
theorem nonpositivePart_reciprocal_lift (t : R) (q : L) :
    T 1 * leftLaurentMap t (boundaryLift t (reciprocalField (nonpositivePart q))) =
      reciprocalField (nonpositivePart q) :=
  boundaryLift_value t _ (reciprocal_nonpositive_coeff q)

end FLT.Mazur.LaurentBoundaryCorrectionSplit
