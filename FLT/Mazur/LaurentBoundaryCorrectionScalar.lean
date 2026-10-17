/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentBoundaryCorrectionSplit

/-!
# Scalar control of the complete Laurent boundary splitting

Each splitting and lifting operation commutes with scalar multiplication.
Consequently, equality of weighted residual fields controls the full node
lifts even when division by the parameter is not unique.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentBoundaryCorrectionSplit
open LaurentPolynomial LaurentBoundaryVectorField PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]
local notation "L" => R[T;T⁻¹]

/-- The strictly positive truncation commutes with every coefficient scalar. -/
theorem positivePart_smul (r : R) (q : L) : positivePart (r • q) = r • positivePart q := by
  ext k
  simp only [positivePart_coeff, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The entire complementary part has the same scalar compatibility. -/
theorem nonpositivePart_smul (r : R) (q : L) :
    nonpositivePart (r • q) = r • nonpositivePart q := by
  rw [nonpositivePart, positivePart_smul, ← smul_sub, nonpositivePart]

/-- Reciprocal vector fields preserve coefficient scalars, including the derivative sign. -/
theorem reciprocalField_smul (r : R) (q : L) :
    reciprocalField (r • q) = r • reciprocalField q := by
  ext k
  simp only [reciprocalField_coeff, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, mul_neg]

/-- The full finite outgoing node lift is linear over the coefficient ring. -/
theorem outgoingPolynomialLift_smul (t r : R) (q : L) :
    outgoingPolynomialLift t (r • q) = r • outgoingPolynomialLift t q :=
  (Finsupp.linearCombination R _).map_smul r q.coeff

/-- Dividing out the boundary coordinate preserves scalar compatibility of the whole lift. -/
theorem boundaryLift_smul (t r : R) (q : L) : boundaryLift t (r • q) = r • boundaryLift t q := by
  rw [boundaryLift, mul_smul_comm, outgoingPolynomialLift_smul, boundaryLift]

/-- Weighted equality controls the entire positive node lift. -/
theorem positiveLift_weighted {e : R} {p q : L} (h : C e * p = C e * q) (t : R) :
    algebraMap R (ChartRing t) e * boundaryLift t (positivePart p) =
      algebraMap R (ChartRing t) e * boundaryLift t (positivePart q) := by
  have hs : e • p = e • q := by simpa only [smul_eq_C_mul] using h
  have hh := congrArg (fun z ↦ boundaryLift t (positivePart z)) hs
  simp only [positivePart_smul, boundaryLift_smul] at hh
  exact (Algebra.smul_def e (boundaryLift t (positivePart p))).symm.trans
    (hh.trans (Algebra.smul_def e (boundaryLift t (positivePart q))))

/-- Weighted equality also controls every complementary reciprocal node coefficient. -/
theorem reciprocalLift_weighted {e : R} {p q : L} (h : C e * p = C e * q) (t : R) :
    algebraMap R (ChartRing t) e * boundaryLift t (reciprocalField (nonpositivePart p)) =
      algebraMap R (ChartRing t) e * boundaryLift t (reciprocalField (nonpositivePart q)) := by
  have hs : e • p = e • q := by simpa only [smul_eq_C_mul] using h
  have hh := congrArg (fun z ↦ boundaryLift t (reciprocalField (nonpositivePart z))) hs
  simp only [nonpositivePart_smul, reciprocalField_smul, boundaryLift_smul] at hh
  exact (Algebra.smul_def e (boundaryLift t (reciprocalField (nonpositivePart p)))).symm.trans
    (hh.trans (Algebra.smul_def e (boundaryLift t (reciprocalField (nonpositivePart q)))))

end FLT.Mazur.LaurentBoundaryCorrectionSplit
