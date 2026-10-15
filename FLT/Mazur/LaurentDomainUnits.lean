/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentUnitPoints
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Units of a Laurent polynomial algebra over a domain

Clearing the negative exponents of a unit and its inverse gives two polynomial
factors of a power of X. Primality of X forces each factor to be a monomial.
-/

@[expose] public noncomputable section
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.LaurentDomainUnits
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every Laurent unit over a domain is a constant unit times one Laurent monomial. -/
theorem exists_monomial (v : R[T;T⁻¹]ˣ) :
    ∃ (a : Rˣ) (d : ℤ), (v : R[T;T⁻¹]) =
      LaurentPolynomial.C (a : R) * LaurentPolynomial.T d := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow (v : R[T;T⁻¹])
  obtain ⟨m, q, hq⟩ := LaurentPolynomial.exists_T_pow (↑v⁻¹ : R[T;T⁻¹])
  have hpq : p * q = Polynomial.X ^ (n + m) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow]
    calc
      _ = (↑v * ↑v⁻¹ : R[T;T⁻¹]) *
          (LaurentPolynomial.T (n : ℤ) * LaurentPolynomial.T (m : ℤ)) := by ring
      _ = _ := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
          ← LaurentPolynomial.T_add, Nat.cast_add]
  obtain ⟨k, _, hk⟩ := (dvd_prime_pow Polynomial.prime_X (n + m)).mp ⟨q, hpq.symm⟩
  obtain ⟨w, hw⟩ := hk.symm
  obtain ⟨a, hau, ha⟩ := Polynomial.isUnit_iff.mp w.isUnit
  obtain ⟨a, rfl⟩ := hau
  refine ⟨a, (k : ℤ) - n, ?_⟩
  have hmono : p = Polynomial.C (a : R) * Polynomial.X ^ k := by
    rw [← hw, ← ha]
    exact mul_comm _ _
  rw [hmono, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow] at hp
  calc
    (v : R[T;T⁻¹]) = (↑v * LaurentPolynomial.T (n : ℤ)) *
        LaurentPolynomial.T (-(n : ℤ)) := by
      rw [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
        LaurentPolynomial.T_zero, mul_one]
    _ = _ := by rw [← hp, mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg]

end FLT.Mazur.LaurentDomainUnits
