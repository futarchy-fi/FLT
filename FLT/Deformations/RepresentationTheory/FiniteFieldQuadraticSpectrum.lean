/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Frobenius-conjugate roots of prime-field quadratics

A non-prime-field root of a monic quadratic determines its other root by
Frobenius. These algebraic identities do not assert finite-flat inertia weights.
-/

@[expose] public noncomputable section
namespace Polynomial

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p]
  (f : ZMod p →+* k) (P : (ZMod p)[X])

/-- Prime-field polynomials have Frobenius-stable roots in every characteristic-p field. -/
theorem isRoot_map_pow_prime {a : k} (ha : (P.map f).IsRoot a) :
    (P.map f).IsRoot (a ^ p) := by
  have hf : (frobenius k p).comp f = f := Subsingleton.elim _ _
  have h := ha.map (f := frobenius k p)
  simpa only [map_map, hf, frobenius_def] using h

/-- Two distinct roots determine a monic quadratic, including over a finite field. -/
theorem eq_factors_of_monic_quadratic {Q : k[X]} (hQ : Q.Monic)
    (hdeg : Q.natDegree = 2) {a b : k} (ha : Q.IsRoot a) (hb : Q.IsRoot b)
    (hab : a ≠ b) : Q = (X - C a) * (X - C b) := by
  apply eq_of_monic_of_dvd_of_natDegree_le
    ((monic_X_sub_C a).mul (monic_X_sub_C b)) hQ
  · exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).mul_dvd
      (dvd_iff_isRoot.mpr ha) (dvd_iff_isRoot.mpr hb)
  · rw [natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)]
    simp [hdeg]

/-- A root distinct from its Frobenius conjugate gives the complete quadratic spectrum. -/
theorem map_eq_frobenius_factors (hP : P.Monic) (hdeg : P.natDegree = 2)
    {a : k} (ha : (P.map f).IsRoot a) (hne : a ≠ a ^ p) :
    P.map f = (X - C a) * (X - C (a ^ p)) := by
  exact eq_factors_of_monic_quadratic (hP.map f)
    ((natDegree_map_eq_of_injective f.injective P).trans hdeg)
    ha (isRoot_map_pow_prime f P ha) hne

/-- In the nontrivial quadratic orbit, Frobenius squared fixes the root. -/
theorem pow_prime_sq_eq_of_quadratic (hP : P.Monic) (hdeg : P.natDegree = 2)
    {a : k} (ha : (P.map f).IsRoot a) (hne : a ≠ a ^ p) :
    a ^ (p * p) = a := by
  have hb := isRoot_map_pow_prime f P (isRoot_map_pow_prime f P ha)
  rw [map_eq_frobenius_factors f P hP hdeg ha hne] at hb
  simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hb
  rcases hb with h | h
  · simpa only [pow_mul] using h
  · exact (hne ((frobenius k p).injective h).symm).elim

end Polynomial
