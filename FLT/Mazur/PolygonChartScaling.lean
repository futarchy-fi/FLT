/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Scalar multiplication in the two projective charts

Scaling by a unit on the first affine chart and its inverse on the second
respects the Laurent transition. These formulas work over any commutative
base ring. They do not assert representability of a group action.
-/

@[expose] public noncomputable section

open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.PolygonChartScaling

variable {R : Type*} [CommRing R]

/-- Substitute a unit multiple of the affine coordinate. -/
def affine (a : Rˣ) : R[X] →+* R[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (a : R) * Polynomial.X)

@[simp]
theorem affine_C (a : Rˣ) (r : R) : affine a (Polynomial.C r) = Polynomial.C r := by
  simp [affine]

@[simp]
theorem affine_X (a : Rˣ) : affine a Polynomial.X = Polynomial.C (a : R) * Polynomial.X := by
  simp [affine]

@[simp]
theorem affine_one : affine (1 : Rˣ) = RingHom.id _ := by
  ext <;> simp

theorem affine_mul (a b : Rˣ) : affine (a * b) = (affine a).comp (affine b) := by
  ext
  · simp only [RingHom.comp_apply, affine_C]
  · simp only [RingHom.comp_apply, affine_X, map_mul, affine_C, Units.val_mul]
    ac_rfl

theorem affine_zero (a : Rˣ) :
    (Polynomial.evalRingHom 0).comp (affine a) = Polynomial.evalRingHom 0 := by
  ext <;> simp

/-- The scaled Laurent coordinate is a unit with the explicit inverse coordinate. -/
def coordinateUnit (a : Rˣ) : R[T;T⁻¹]ˣ where
  val := LaurentPolynomial.C (a : R) * LaurentPolynomial.T 1
  inv := LaurentPolynomial.C (↑a⁻¹ : R) * LaurentPolynomial.T (-1)
  val_inv := by
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
    simp
  inv_val := by
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add]
    simp

/-- Substitute the scaled Laurent coordinate. -/
def laurent (a : Rˣ) : R[T;T⁻¹] →+* R[T;T⁻¹] :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C (coordinateUnit a)

@[simp]
theorem laurent_C (a : Rˣ) (r : R) :
    laurent a (LaurentPolynomial.C r) = LaurentPolynomial.C r :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp]
theorem laurent_T_one (a : Rˣ) :
    laurent a (LaurentPolynomial.T 1) =
      LaurentPolynomial.C (a : R) * LaurentPolynomial.T 1 := by
  simp [laurent, LaurentPolynomial.eval₂_T, coordinateUnit]

@[simp]
theorem laurent_T_neg_one (a : Rˣ) :
    laurent a (LaurentPolynomial.T (-1)) =
      LaurentPolynomial.C (↑a⁻¹ : R) * LaurentPolynomial.T (-1) := by
  simp [laurent, LaurentPolynomial.eval₂_T, coordinateUnit]

/-- Scaling agrees with restriction to the first punctured chart. -/
theorem toLaurent_affine (a : Rˣ) :
    Polynomial.toLaurent.comp (affine a) = (laurent a).comp Polynomial.toLaurent := by
  ext <;> simp

/-- On the inverse-coordinate chart the scalar must be inverted. -/
theorem invert_toLaurent_affine (a : Rˣ) :
    LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent.comp (affine a⁻¹)) =
      (laurent a).comp (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := by
  ext <;> simp

end FLT.Mazur.PolygonChartScaling
