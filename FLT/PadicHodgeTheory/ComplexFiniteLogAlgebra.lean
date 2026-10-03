/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexFiniteThetaScalars
public import Mathlib.RingTheory.PowerSeries.Log

/-! # Rational logarithm coefficients in the actual de Rham rings -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Use the already constructed p-adic scalar embedding for rational coefficients. -/
scoped instance complexDeRhamRatAlgebra : Algebra ℚ (ComplexBDeRhamPlus p) :=
  ((complexPadicToDeRham p).comp (algebraMap ℚ ℚ_[p])).toAlgebra

/-- Rational scalars at a finite level use its existing compatible scalar map. -/
scoped instance complexFiniteThetaRatAlgebra (r : ℕ) :
    Algebra ℚ (ComplexFiniteThetaQuotient p r) :=
  ((complexFiniteThetaQuotientScalars p r).comp (algebraMap ℚ ℚ_[p])).toAlgebra

/-- Rational denominator inverses equal the genuine inverses used to construct t. -/
theorem complexDeRhamRat_inverse_nat (n : ℕ) (hn : n ≠ 0) :
    algebraMap ℚ (ComplexBDeRhamPlus p) (n : ℚ)⁻¹ =
      Ring.inverse (n : ComplexBDeRhamPlus p) := by
  apply (complexDeRhamNat_isUnit p n hn).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (complexDeRhamNat_isUnit p n hn)]
  calc
    (n : ComplexBDeRhamPlus p) * algebraMap ℚ (ComplexBDeRhamPlus p) (n : ℚ)⁻¹ =
        algebraMap ℚ (ComplexBDeRhamPlus p) ((n : ℚ) * (n : ℚ)⁻¹) := by
          rw [map_mul, map_natCast]
    _ = 1 := by rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), map_one]

/-- The coefficients defining t are exactly the formal logarithm coefficients. -/
theorem complexLogCoefficient_eq_powerSeries (n : ℕ) :
    complexLogCoefficient p n = PowerSeries.coeff n (PowerSeries.log (ComplexBDeRhamPlus p)) := by
  cases n with
  | zero => simp [complexLogCoefficient]
  | succ n =>
    rw [PowerSeries.coeff_log, ite_eq_right (Nat.succ_ne_zero n), div_eq_mul_inv,
      map_mul, map_pow, map_neg, map_one, complexDeRhamRat_inverse_nat p _ (Nat.succ_ne_zero n)]
    simp [complexLogCoefficient, pow_succ]

/-- Every finite evaluation carries the original coefficients to the standard rational ones. -/
theorem complexLogCoefficient_eval (r n : ℕ) :
    AdicCompletion.evalₐ (ComplexDeRhamIdeal p) r (complexLogCoefficient p n) =
      PowerSeries.coeff n (PowerSeries.log (ComplexFiniteThetaQuotient p r)) := by
  rw [complexLogCoefficient_eq_powerSeries, PowerSeries.coeff_log, PowerSeries.coeff_log]
  split_ifs
  · exact map_zero _
  · exact RingHom.map_rat_algebraMap
      (show ComplexBDeRhamPlus p →+* ComplexFiniteThetaQuotient p r from
        (AdicCompletion.evalₐ (ComplexDeRhamIdeal p) r).toRingHom) _

end PadicHodgeTheory
