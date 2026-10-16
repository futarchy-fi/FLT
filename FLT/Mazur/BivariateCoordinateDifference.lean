/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Ring

/-!
# Explicit coefficients of a bivariate coordinate difference

Finite geometric sums give exact coefficients of the two coordinate errors.
No division, reducedness, or invertibility hypothesis is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BivariateCoordinateDifference
variable {A R : Type*} [CommRing A] [CommRing R]

/-- The polynomial divided difference of a power, valid when the two values coincide. -/
def powerDifference (x y : R) (m : ℕ) : R :=
  ∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)

/-- Clear the difference of the two arguments without any cancellation assumption. -/
theorem powerDifference_mul (x y : R) (m : ℕ) :
    powerDifference x y m * (x - y) = x ^ m - y ^ m := geom_sum₂_mul x y m

/-- The explicit coefficient of the first coordinate error. -/
def leftCoefficient (f : A →+* R) (p : MvPolynomial (Fin 2) A) (x y : Fin 2 → R) : R :=
  ∑ d ∈ p.support, f (p.coeff d) * powerDifference (x 0) (y 0) (d 0) * x 1 ^ d 1

/-- The explicit coefficient of the second coordinate error. -/
def rightCoefficient (f : A →+* R) (p : MvPolynomial (Fin 2) A) (x y : Fin 2 → R) : R :=
  ∑ d ∈ p.support, f (p.coeff d) * y 0 ^ d 0 * powerDifference (x 1) (y 1) (d 1)

/-- The exact difference of polynomial evaluations, with explicit finite-sum coefficients. -/
theorem evaluation_sub (f : A →+* R) (p : MvPolynomial (Fin 2) A) (x y : Fin 2 → R) :
    MvPolynomial.eval₂Hom f x p - MvPolynomial.eval₂Hom f y p =
      leftCoefficient f p x y * (x 0 - y 0) +
        rightCoefficient f p x y * (x 1 - y 1) := by
  change MvPolynomial.eval₂ f x p - MvPolynomial.eval₂ f y p = _
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib,
    leftCoefficient, rightCoefficient, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Fin.prod_univ_two]
  calc
    _ = f (p.coeff d) * ((x 0 ^ d 0 - y 0 ^ d 0) * x 1 ^ d 1 +
        y 0 ^ d 0 * (x 1 ^ d 1 - y 1 ^ d 1)) := by ring
    _ = _ := by rw [← powerDifference_mul, ← powerDifference_mul]; ring

end FLT.Mazur.BivariateCoordinateDifference
