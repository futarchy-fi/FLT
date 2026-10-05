/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalMultiplication

/-!
# The quadratic coefficient of residue-characteristic multiplication

Multiplication by n commutes with doubling. Comparing their quadratic
coefficients shows that, when n vanishes and two is a unit in the coefficient
ring, the quadratic coefficient of multiplication by n vanishes as well.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R]

/-- The quadratic coefficient of composition with a zero-constant series. -/
theorem coeff_two_subst (f g : PowerSeries R) (hg : g.constantCoeff = 0) :
    PowerSeries.coeff 2 (f.subst g) = PowerSeries.coeff 1 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 2 f * PowerSeries.coeff 1 g ^ 2 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero hg)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 3) (by
    intro n hn
    by_contra h
    have hn3 : 2 < n := by simp only [Finset.mem_coe, Finset.mem_range] at h; omega
    have hz := PowerSeries.X_pow_dvd_iff.mp
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hg) n) 2 hn3
    exact hn (by simp [hz]))]
  have hs : PowerSeries.coeff 2 (g ^ 2) = PowerSeries.coeff 1 g ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul]
    simp [Finset.Nat.sum_antidiagonal_succ, PowerSeries.coeff_zero_eq_constantCoeff, hg, pow_two]
  simp [Finset.sum_range_succ, hs, smul_eq_mul]

/-- The multiplication series commutes with the multiplication series of every other scalar. -/
theorem multiplicationSeries_comp_comm (W : WeierstrassCurve R) (m n : ℕ) :
    (multiplicationSeries W m).subst (multiplicationSeries W n) =
      (multiplicationSeries W n).subst (multiplicationSeries W m) := by
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  have hz (k : ℕ) : MvPowerSeries.constantCoeff (multiplicationSeries W k) = 0 :=
    constantCoeff_multiply W k hx
  rw [multiplicationSeries_subst W m (hz n), multiplicationSeries_subst W n (hz m)]
  change multiply W m (multiply W n PowerSeries.X) = multiply W n (multiply W m PowerSeries.X)
  rw [← multiply_mul W n m hx, ← multiply_mul W m n hx, Nat.mul_comm n m]

/-- In odd residue characteristic, multiplication by a vanishing scalar has no quadratic term. -/
theorem coeff_two_multiplicationSeries_eq_zero (W : WeierstrassCurve R) (n : ℕ)
    (hn : (n : R) = 0) (h2 : IsUnit (2 : R)) :
    PowerSeries.coeff 2 (multiplicationSeries W n) = 0 := by
  have h := congrArg (PowerSeries.coeff 2) (multiplicationSeries_comp_comm W n 2)
  have hx : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 := by
    simp [PowerSeries.X]
  have hz (k : ℕ) : PowerSeries.constantCoeff (multiplicationSeries W k) = 0 :=
    constantCoeff_multiply W k hx
  rw [coeff_two_subst _ _ (hz 2), coeff_two_subst _ _ (hz n),
    coeff_one_multiplicationSeries, coeff_one_multiplicationSeries, hn] at h
  apply h2.mul_right_eq_zero.mp
  linear_combination h

/-- The remainder after the linear and quadratic terms is divisible by T³. -/
theorem X_cube_dvd_multiplicationSeries_sub_quadratic (W : WeierstrassCurve R) (n : ℕ) :
    PowerSeries.X ^ 3 ∣ multiplicationSeries W n - PowerSeries.C (n : R) * PowerSeries.X -
      PowerSeries.C (PowerSeries.coeff 2 (multiplicationSeries W n)) * PowerSeries.X ^ 2 := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro m hm
  interval_cases m
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff,
      multiplicationSeries, PowerSeries.X]
  · simp
  · simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      PowerSeries.coeff_X_pow]
    simp

end FLT.Mazur.FormalInfinity
