/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Laurent polynomial points

Algebra maps from the Laurent polynomial algebra are naturally equivalent to
units. This is the algebraic functor of points of the multiplicative group.
-/

@[expose] public noncomputable section

open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.LaurentUnitPoints

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluate the Laurent coordinate at a unit. -/
def evalUnit (a : Aˣ) : R[T;T⁻¹] →ₐ[R] A where
  __ := LaurentPolynomial.eval₂ (algebraMap R A) a
  commutes' r := LaurentPolynomial.eval₂_C _ _ r

@[simp]
theorem evalUnit_C (a : Aˣ) (r : R) :
    evalUnit a (LaurentPolynomial.C r) = algebraMap R A r :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp]
theorem evalUnit_T (a : Aˣ) (m : ℤ) :
    evalUnit (R := R) a (LaurentPolynomial.T m) = (a ^ m : Aˣ).val :=
  LaurentPolynomial.eval₂_T _ _ _

/-- The images of the two inverse coordinates give a unit. -/
def pointUnit (f : R[T;T⁻¹] →ₐ[R] A) : Aˣ where
  val := f (LaurentPolynomial.T 1)
  inv := f (LaurentPolynomial.T (-1))
  val_inv := by rw [← map_mul, ← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← map_mul, ← LaurentPolynomial.T_add]; simp

/-- An algebra map is determined by the two Laurent generators. -/
theorem hom_ext {f g : R[T;T⁻¹] →ₐ[R] A}
    (hpos : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1))
    (hneg : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1))) : f = g := by
  apply AlgHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on with
  | h_C r => exact (f.commutes r).trans (g.commutes r).symm
  | h_add hp hq => simp only [map_add, hp, hq]
  | h_C_mul_T n r ih =>
    rw [LaurentPolynomial.T_add, ← mul_assoc, map_mul, ih, hpos]
    simp only [map_mul]
  | h_C_mul_T_Z n r ih =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc, map_mul, ih, hneg]
    simp only [map_mul]

@[simp]
theorem evalUnit_pointUnit (f : R[T;T⁻¹] →ₐ[R] A) : evalUnit (pointUnit f) = f := by
  apply hom_ext <;> simp [pointUnit]

@[simp]
theorem pointUnit_evalUnit (a : Aˣ) : pointUnit (evalUnit (R := R) a) = a := by
  apply Units.ext
  simp [pointUnit]

/-- Laurent algebra points are units. -/
def pointsEquiv : (R[T;T⁻¹] →ₐ[R] A) ≃ Aˣ where
  toFun := pointUnit
  invFun := evalUnit
  left_inv := evalUnit_pointUnit
  right_inv := pointUnit_evalUnit

@[simp]
theorem pointsEquiv_symm_apply (a : Aˣ) :
    (pointsEquiv (R := R)).symm a = evalUnit a := rfl

/-- Evaluation commutes with a change of target algebra. -/
theorem evalUnit_natural {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (a : Aˣ) :
    f.comp (evalUnit a) = evalUnit (Units.map f.toMonoidHom a) := by
  apply hom_ext <;> simp [Units.map]

end FLT.Mazur.LaurentUnitPoints
