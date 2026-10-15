/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeLocalization
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic

/-!
# Derivations on the original split node fix its branch origins

The relation xy = 0 forces a derivation's x coordinate to vanish on the
opposite branch, and likewise for y. Equality of the two constant terms
then forces each surviving polynomial vector field to fix its origin.
This works over arbitrary coefficient rings, including nonreduced rings.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.NodeDerivationBoundary
open PolygonNodeEqualizer PolygonNodeLocalization
variable {R : Type*} [CommRing R]
local notation "N" => A (R := R)

/-- Multiplication by the polynomial variable is injective over any coefficient ring. -/
theorem polynomial_X_mul_zero {p : R[X]} (hp : Polynomial.X * p = 0) : p = 0 := by
  ext n
  have he := congrArg (fun q : R[X] ↦ q.coeff (n + 1)) hp
  simpa using he

/-- The derivative of x has zero restriction to the other branch. -/
theorem second_derivation_x (d : Derivation R (N) (N)) : second (d x) = 0 := by
  apply polynomial_X_mul_zero
  have he := congrArg second (d.leibniz x y)
  simpa only [x_mul_y, map_zero, smul_eq_mul, map_add, map_mul, second_x,
    second_y, zero_mul, zero_add] using he.symm

/-- The derivative of y has zero restriction to the other branch. -/
theorem first_derivation_y (d : Derivation R (N) (N)) : first (d y) = 0 := by
  apply polynomial_X_mul_zero
  have he := congrArg first (d.leibniz x y)
  simpa only [x_mul_y, map_zero, smul_eq_mul, map_add, map_mul, first_x,
    first_y, zero_mul, add_zero] using he.symm

/-- The actual first polynomial vector field has zero constant term. -/
theorem first_derivation_x_coeff_zero (d : Derivation R (N) (N)) :
    (first (d x)).coeff 0 = 0 := by
  have he := AlgHom.congr_fun (first_second_agree (R := R)) (d x)
  change (first (d x)).eval 0 = (second (d x)).eval 0 at he
  rw [second_derivation_x, Polynomial.eval_zero] at he
  exact (Polynomial.coeff_zero_eq_eval_zero _).trans he

/-- The actual second polynomial vector field has zero constant term. -/
theorem second_derivation_y_coeff_zero (d : Derivation R (N) (N)) :
    (second (d y)).coeff 0 = 0 := by
  have he := AlgHom.congr_fun (first_second_agree (R := R)) (d y)
  change (first (d y)).eval 0 = (second (d y)).eval 0 at he
  rw [first_derivation_y, Polynomial.eval_zero] at he
  exact (Polynomial.coeff_zero_eq_eval_zero _).trans he.symm

/-- Restricting a genuine node derivation supplies an actual first boundary polynomial. -/
theorem left_derivation_boundary (d : Derivation R (N) (N)) :
    ∃ p : R[X], p.toLaurent = leftMap (d x) ∧ p.coeff 0 = 0 :=
  ⟨first (d x), rfl, first_derivation_x_coeff_zero d⟩

/-- Restricting a genuine node derivation supplies an actual second boundary polynomial. -/
theorem right_derivation_boundary (d : Derivation R (N) (N)) :
    ∃ p : R[X], p.toLaurent = rightMap (d y) ∧ p.coeff 0 = 0 :=
  ⟨second (d y), rfl, second_derivation_y_coeff_zero d⟩

end FLT.Mazur.NodeDerivationBoundary
