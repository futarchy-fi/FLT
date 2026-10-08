/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalPrimeCoefficients

/-!
# Integral remainder of the formal p-series

The low-degree divisibility theorem separates the p-series into its linear
term, a p-divisible quadratic remainder, and a remainder divisible by T^p.
All coefficients remain in the original ring, including ramified DVRs.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Integral decomposition of multiplication by a prime, before any evaluation. -/
theorem multiplicationSeries_prime_expansion (p : ℕ) [Fact p.Prime] :
    ∃ g h : PowerSeries R, multiplicationSeries W p =
      C (p : R) * X + C (p : R) * X ^ 2 * g + X ^ p * h := by
  classical
  let g : PowerSeries R := PowerSeries.mk fun i =>
    if hi : i + 2 < p then
      Classical.choose (prime_dvd_coeff_multiplicationSeries W p (i + 2) hi)
    else 0
  have hg (i : ℕ) (hi : i + 2 < p) :
      (p : R) * coeff i g = coeff (i + 2) (multiplicationSeries W p) := by
    simp only [g, coeff_mk, dite_eq_left hi]
    exact (Classical.choose_spec
      (prime_dvd_coeff_multiplicationSeries W p (i + 2) hi)).symm
  have hd : X ^ p ∣ multiplicationSeries W p - C (p : R) * X - C (p : R) * X ^ 2 * g := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rcases k with _ | _ | k
    · simp [coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff,
        multiplicationSeries, PowerSeries.X]
    · simp [mul_assoc, coeff_X_pow_mul']
    · rw [map_sub, map_sub, coeff_C_mul, coeff_X, ite_eq_right (by omega), mul_zero,
        sub_zero, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
        ite_eq_left (by omega : 2 ≤ k + 2), show k + 1 + 1 - 2 = k by omega, hg k hk, sub_self]
  obtain ⟨h, hh⟩ := hd
  exact ⟨g, h, by linear_combination hh⟩

end FLT.Mazur.FormalInfinity
