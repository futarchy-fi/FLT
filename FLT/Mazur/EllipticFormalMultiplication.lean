/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalFirstOrder
public import FLT.Mazur.EllipticFormalGroupLaw

/-!
# Integral formal multiplication

Repeated addition constructs [n](T) over the original coefficient ring. It has
constant coefficient zero and linear coefficient n. The remaining terms are
divisible by T². The construction commutes with substitution and coefficient
changes, and obeys the addition and composition identities for natural scalars.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*} (W : WeierstrassCurve R)

/-- Repeated formal addition of a parameter. -/
noncomputable def multiply : ℕ → MvPowerSeries σ R → MvPowerSeries σ R
  | 0, _ => 0
  | n + 1, t => add W (multiply n t) t

/-- The integral multiplication-by-n series. -/
noncomputable def multiplicationSeries (n : ℕ) : PowerSeries R :=
  multiply W n PowerSeries.X

/-- Multiplication preserves zero constant coefficients. -/
@[simp] theorem constantCoeff_multiply (n : ℕ) {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) : (multiply W n t).constantCoeff = 0 := by
  induction n with
  | zero => simp [multiply]
  | succ n ih => exact constantCoeff_add W ih ht

/-- Multiplication by one is the identity. -/
@[simp] theorem multiply_one {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    multiply W 1 t = t := zero_add W ht

/-- Addition of natural scalars agrees with formal addition. -/
theorem multiply_add (m n : ℕ) {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    multiply W (m + n) t = add W (multiply W m t) (multiply W n t) := by
  induction n with
  | zero => exact (add_zero W (constantCoeff_multiply W m ht)).symm
  | succ n ih =>
    change add W (multiply W (m + n) t) t =
      add W (multiply W m t) (add W (multiply W n t) t)
    rw [ih]
    exact add_assoc W (constantCoeff_multiply W m ht) (constantCoeff_multiply W n ht) ht

/-- Product of natural scalars agrees with repeated formal multiplication. -/
theorem multiply_mul (m n : ℕ) {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    multiply W (m * n) t = multiply W n (multiply W m t) := by
  induction n with
  | zero => simp [multiply]
  | succ n ih => rw [Nat.mul_succ, multiply_add W _ _ ht, ih, multiply]

/-- Repeated addition commutes with zero-constant substitution. -/
theorem substitution_multiply {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) (ha0 : ∀ i, (a i).constantCoeff = 0)
    (n : ℕ) {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    MvPowerSeries.substAlgHom ha (multiply W n t) =
      multiply W n (MvPowerSeries.substAlgHom ha t) := by
  induction n with
  | zero => exact map_zero (MvPowerSeries.substAlgHom ha)
  | succ n ih =>
    rw [multiply, substitution_add W ha ha0 (constantCoeff_multiply W n ht) ht, ih, multiply]

/-- The multiplication series represents repeated addition at every formal parameter. -/
theorem multiplicationSeries_subst (n : ℕ) {t : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) : (multiplicationSeries W n).subst t = multiply W n t := by
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => t) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero ht).const
  rw [multiplicationSeries, PowerSeries.subst, ← MvPowerSeries.coe_substAlgHom ha]
  rw [substitution_multiply W ha (fun _ => ht) n (by simp [PowerSeries.X])]
  simp [PowerSeries.X, MvPowerSeries.subst_X ha]

/-- Coefficient-ring changes preserve formal multiplication. -/
theorem map_multiply {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    MvPowerSeries.map f (multiply W n t) = multiply (W.map f) n (MvPowerSeries.map f t) := by
  induction n with
  | zero => simp [multiply]
  | succ n ih =>
    rw [multiply, map_addition W f (constantCoeff_multiply W n ht) ht, ih, multiply]

/-- The linear coefficient of multiplication is n times that of the parameter. -/
theorem coeff_one_multiply (n : ℕ) {t : PowerSeries R}
    (ht : MvPowerSeries.constantCoeff t = 0) :
    PowerSeries.coeff 1 (multiply W n t) = n * PowerSeries.coeff 1 t := by
  induction n with
  | zero => simp [multiply]
  | succ n ih =>
    rw [multiply, coeff_one_add W (constantCoeff_multiply W n ht) ht, ih]
    push_cast
    ring

/-- The multiplication series has linear coefficient n. -/
@[simp] theorem coeff_one_multiplicationSeries (n : ℕ) :
    PowerSeries.coeff 1 (multiplicationSeries W n) = n := by
  simpa [multiplicationSeries] using
    coeff_one_multiply W n (t := PowerSeries.X) (by simp [PowerSeries.X])

/-- All nonlinear terms of multiplication are divisible by T². -/
theorem X_sq_dvd_multiplicationSeries_sub_linear (n : ℕ) :
    PowerSeries.X ^ 2 ∣ multiplicationSeries W n - PowerSeries.C (n : R) * PowerSeries.X := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro m hm
  interval_cases m
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff,
      multiplicationSeries, PowerSeries.X]
  · simp

end FLT.Mazur.FormalInfinity
