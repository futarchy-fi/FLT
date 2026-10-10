/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Leading coefficients of composition

If one series starts in degree k, composition in either order only sees the
linear term of the other series in degree k. These identities work over rings
with zero divisors, as needed for reduction modulo the integer p.
-/

@[expose] public section

namespace FLT.Mazur

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The diagonal coefficient of a power of a zero-constant series. -/
theorem coeff_pow_diagonal (g : PowerSeries R) (hg : g.constantCoeff = 0) (k : ℕ) :
    coeff k (g ^ k) = coeff 1 g ^ k := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.mpr hg
  rw [mul_pow, coeff_X_pow_mul', Nat.sub_self, ite_eq_left (le_refl k)]
  simp only [coeff_zero_eq_constantCoeff, map_pow]
  rw [show coeff 1 (X * h) = h.constantCoeff by
    simp]

/-- A first nonzero outer coefficient composes with the power of the inner linear term. -/
theorem coeff_subst_of_outer_vanishing (f g : PowerSeries R) (k : ℕ)
    (hg : g.constantCoeff = 0) (hf : ∀ i < k, coeff i f = 0) :
    coeff k (f.subst g) = coeff k f * coeff 1 g ^ k := by
  classical
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero hg), finsum_eq_single _ k]
  · rw [smul_eq_mul, coeff_pow_diagonal g hg k]
  · intro i hi
    rcases lt_or_gt_of_ne hi with hi | hi
    · rw [hf i hi, zero_smul]
    · have hz := X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hg) i) k hi
      rw [hz, smul_zero]

/-- A first nonzero inner coefficient composes with the outer linear term. -/
theorem coeff_subst_of_inner_vanishing (f g : PowerSeries R) (k : ℕ) (hk : 0 < k)
    (hg : ∀ i < k, coeff i g = 0) :
    coeff k (f.subst g) = coeff 1 f * coeff k g := by
  classical
  have hg0 : g.constantCoeff = 0 := by
    simpa only [coeff_zero_eq_constantCoeff] using hg 0 hk
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero hg0), finsum_eq_single _ 1]
  · simp only [pow_one, smul_eq_mul]
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [coeff_one, hk.ne']
    · have hki : k < k * i := by
        exact lt_mul_of_one_lt_right hk (by omega)
      have hd : X ^ (k * i) ∣ g ^ i := by
        rw [pow_mul]
        exact pow_dvd_pow_of_dvd (X_pow_dvd_iff.mpr hg) i
      rw [X_pow_dvd_iff.mp hd k hki, smul_zero]

end FLT.Mazur
