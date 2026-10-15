/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentPolynomialEvaluation
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Exact quadratic remainders with nilpotent coefficients

Translation, differentiation and removal of the first two coefficients all
preserve the arithmetic ideal. The resulting Taylor identity is exact.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentPolynomialInverse
variable {R : Type*} [CommRing R] (I : Ideal R) (h : R[X]) (hh : h ∈ I.map C)

include hh in
/-- Differentiation preserves every arithmetic coefficient ideal. -/
theorem derivative_mem : h.derivative ∈ I.map C := by
  apply Ideal.mem_map_C_iff.mpr
  intro n
  rw [coeff_derivative]
  exact I.mul_mem_right _ (Ideal.mem_map_C_iff.mp hh (n + 1))

include hh in
/-- Translation preserves every arithmetic coefficient ideal. -/
theorem taylor_mem (z : R) : taylor z h ∈ I.map C := by
  simpa only [taylor_apply, comp] using eval₂_mem I C h hh (X + C z)

include hh in
/-- Removing the constant coefficient preserves every arithmetic coefficient ideal. -/
theorem divX_mem : h.divX ∈ I.map C := by
  apply Ideal.mem_map_C_iff.mpr
  intro n
  rw [coeff_divX]
  exact Ideal.mem_map_C_iff.mp hh (n + 1)

/-- The explicit polynomial containing all Taylor terms from degree two onward. -/
def quadraticRemainder (z : R) : R[X] := (taylor z h).divX.divX

/-- The exact Taylor identity, valid in arbitrary characteristic. -/
theorem quadraticRemainder_equation (z : R) :
    h.comp (X + C z) = C (h.eval z) + C (h.derivative.eval z) * X +
      X ^ 2 * quadraticRemainder h z := by
  have h0 := X_mul_divX_add (taylor z h)
  have h1 := X_mul_divX_add (taylor z h).divX
  rw [coeff_divX, zero_add, taylor_coeff_one] at h1
  rw [taylor_coeff_zero, taylor_apply] at h0
  change X * (taylor z h).divX.divX + C (h.derivative.eval z) =
    (taylor z h).divX at h1
  change h.comp (X + C z) = C (h.eval z) + C (h.derivative.eval z) * X +
    X ^ 2 * (taylor z h).divX.divX
  simp only [taylor_apply] at h1 ⊢
  linear_combination -h0 - X * h1

/-- The exact quadratic Taylor identity after arbitrary coefficient extension. -/
theorem quadraticRemainder_eval {S : Type*} [CommRing S] (f : R →+* S) (z : R) (d : S) :
    h.eval₂ f (d + f z) = f (h.eval z) + f (h.derivative.eval z) * d +
      d ^ 2 * (quadraticRemainder h z).eval₂ f d := by
  have he := congrArg (Polynomial.eval₂ f d) (quadraticRemainder_equation h z)
  simpa only [eval₂_comp, eval₂_add, eval₂_C, eval₂_X, eval₂_mul, eval₂_pow] using he

include hh in
/-- The full quadratic remainder retains the nilpotent arithmetic coefficients. -/
theorem quadraticRemainder_mem (z : R) : quadraticRemainder h z ∈ I.map C :=
  divX_mem I _ (divX_mem I _ (taylor_mem I h hh z))

end FLT.Mazur.NilpotentPolynomialInverse
