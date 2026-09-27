/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.DivisionPolynomialDifferential

/-!
# Separability of division polynomials

Derivative identities and coprimality with the two-division polynomial prove
separability for the three- and five-division polynomials in characteristics
different from three and five, respectively. For general odd indices, a
congruence involving the squared derivative suffices for separability.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R)

/-- The derivative of the five-division polynomial factors through the
square two-division polynomial over any commutative ring. -/
theorem derivative_preΨ_five : (E.preΨ 5).derivative =
    5 * E.Ψ₂Sq * (E.invar * E.preΨ₄ - E.Ψ₃ ^ 2) := by
  have hb := congrArg (C : R →+* R[X]) E.b_relation
  simp only [map_mul, map_pow, map_sub, map_ofNat] at hb
  rw [E.preΨ_five]
  simp only [preΨ₄, Ψ₂Sq, Ψ₃, invar,
    derivative_mul, derivative_pow, derivative_X, derivative_C, derivative_ofNat,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast]
  linear_combination -(C E.b₆ * X + C E.b₈ + X ^ 4) *
    (4 * X ^ 3 + C E.b₂ * X ^ 2 + 2 * C E.b₄ * X + C E.b₆) * hb

/-- The squared-derivative congruence for the five-division polynomial holds
over every commutative ring. -/
theorem preΨ_five_dvd_derivative_sq :
    E.preΨ 5 ∣ E.Ψ₂Sq * (E.preΨ 5).derivative ^ 2 - C ((5 : R) ^ 2) * E.Φ 5 := by
  refine ⟨25 * (E.Ψ₂Sq * (E.invar ^ 2 * E.preΨ₄ - E.Ψ₃ * E.Ψ₂Sq ^ 2 +
    E.Ψ₃ * E.preΨ₄) - X * E.preΨ 5), ?_⟩
  have h6 : E.preΨ 6 = E.Ψ₃ * (E.preΨ 5 - E.preΨ₄ ^ 2) := by
    simpa [mul_sub] using E.preΨ_even 3
  have hf : E.preΨ₄ = E.invar * E.Ψ₃ - E.Ψ₂Sq ^ 2 :=
    eq_sub_iff_add_eq.mpr E.preΨ₄_add_Ψ₂Sq_sq
  rw [derivative_preΨ_five, WeierstrassCurve.Φ, ΨSq]
  norm_num only [show ¬Even (5 : ℤ) by decide, ite_false, mul_one]
  rw [h6, preΨ_four, preΨ_five, hf]
  simp only [map_ofNat]
  ring

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- The three-division polynomial of an elliptic curve is separable over
any field of characteristic different from three, including characteristic two. -/
theorem separable_preΨ_three (h3 : (3 : k) ≠ 0) : (W.preΨ 3).Separable := by
  rw [Polynomial.separable_def, preΨ_three, W.derivative_Ψ₃]
  apply IsCoprime.mul_right
  · refine ⟨0, C ((3 : k)⁻¹), ?_⟩
    simp only [zero_mul, zero_add, ← C_ofNat, ← C_mul, inv_mul_cancel₀ h3, C_1]
  · simpa only [Nat.cast_ofNat, preΨ_three, ΨSq_two] using
      W.isCoprime_preΨ_ΨSq_two (show Odd 3 by decide)

/-- A congruence between the squared derivative and the multiplication numerator
forces an odd division polynomial to be separable. The criterion works in
characteristic two as well as in odd characteristic. -/
theorem separable_preΨ_of_derivative_sq {n : ℕ} (hn : Odd n) (hchar : (n : k) ≠ 0)
    (hd : W.preΨ n ∣ W.Ψ₂Sq * (W.preΨ n).derivative ^ 2 - C ((n : k) ^ 2) * W.Φ n) :
    (W.preΨ n).Separable := by
  obtain ⟨q, hq⟩ := hd
  obtain ⟨a, b, hab⟩ := W.isCoprime_Φ_ΨSq_of_isElliptic n
  have he : ¬Even (n : ℤ) := by
    simpa only [Int.even_coe_nat] using (Nat.not_even_iff_odd.mpr hn)
  simp only [ΨSq, ite_eq_right he, mul_one] at hab
  have hi : C (((n : k) ^ 2)⁻¹) * C ((n : k) ^ 2) = (1 : k[X]) := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 hchar), C_1]
  rw [Polynomial.separable_def']
  refine ⟨C (((n : k) ^ 2)⁻¹) * (b * C ((n : k) ^ 2) * W.preΨ n - a * q),
    C (((n : k) ^ 2)⁻¹) * a * W.Ψ₂Sq * (W.preΨ n).derivative, ?_⟩
  linear_combination C (((n : k) ^ 2)⁻¹) * a * hq +
    C (((n : k) ^ 2)⁻¹) * C ((n : k) ^ 2) * hab + hi

/-- A polynomial congruent to a nonzero scalar multiple of the multiplication
numerator is coprime to the corresponding division polynomial. -/
theorem isCoprime_preΨ_of_congr_Φ {n : ℕ} (hchar : (n : k) ≠ 0) {g : k[X]}
    (hd : W.preΨ n ∣ g - C ((n : k) ^ 2) * W.Φ n) :
    IsCoprime (W.preΨ n) g := by
  obtain ⟨q, hq⟩ := hd
  have hc : IsCoprime (W.Φ n) (W.preΨ n) := by
    have h := W.isCoprime_Φ_ΨSq_of_isElliptic n
    rw [ΨSq, pow_two] at h
    exact h.of_mul_right_left.of_mul_right_left
  obtain ⟨a, b, hab⟩ := hc
  have hi : C (((n : k) ^ 2)⁻¹) * C ((n : k) ^ 2) = (1 : k[X]) := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 hchar), C_1]
  refine ⟨C (((n : k) ^ 2)⁻¹) * (b * C ((n : k) ^ 2) - a * q),
    C (((n : k) ^ 2)⁻¹) * a, ?_⟩
  linear_combination C (((n : k) ^ 2)⁻¹) * a * hq +
    C (((n : k) ^ 2)⁻¹) * C ((n : k) ^ 2) * hab + hi

/-- Vanishing of the corrected differential residual implies separability at
any index nonzero in the field, including even indices. -/
theorem separable_preΨ_of_divisionDifferentialDefect {n : ℕ} (hchar : (n : k) ≠ 0)
    (hd : W.divisionDifferentialDefect n = 0) : (W.preΨ n).Separable := by
  unfold divisionDifferentialDefect at hd
  have hc : ((n : ℤ) : k) = (n : k) := by simp
  rw [hc] at hd
  split_ifs at hd with he
  · have hdiv : W.preΨ n ∣ W.Ψ₂Sq ^ 2 * (W.preΨ n).derivative ^ 2 -
        C ((n : k) ^ 2) * W.Φ n := by
      refine ⟨W.Ψ₂Sq ^ 2 * (W.preΨ n).derivative.derivative +
        W.Ψ₂Sq * W.invar * (W.preΨ n).derivative + 4 * W.Ψ₃ * W.preΨ n -
        C ((n : k) ^ 2) * X * W.preΨ n * W.Ψ₂Sq, ?_⟩
      simp only [divisionDifferential, ΨSq, ite_eq_left he] at hd
      linear_combination hd
    have h := W.isCoprime_preΨ_of_congr_Φ hchar hdiv
    rw [Polynomial.separable_def]
    simp only [pow_two] at h
    exact h.of_mul_right_right.of_mul_right_left
  · have hn : Odd n := Nat.not_even_iff_odd.mp (by simpa using he)
    apply W.separable_preΨ_of_derivative_sq hn hchar
    refine ⟨W.Ψ₂Sq * (W.preΨ n).derivative.derivative +
      W.invar * (W.preΨ n).derivative - C ((n : k) ^ 2) * X * W.preΨ n, ?_⟩
    simp only [divisionDifferential, ΨSq, ite_eq_right he, mul_one] at hd
    linear_combination hd

/-- At an even index nonzero in the field, the corrected differential identity
also separates the roots of `preΨ` from the two-torsion x-coordinates. -/
theorem isCoprime_preΨ_Ψ₂Sq_of_divisionDifferentialDefect {n : ℕ}
    (hn : Even n) (hchar : (n : k) ≠ 0) (hd : W.divisionDifferentialDefect n = 0) :
    IsCoprime (W.preΨ n) W.Ψ₂Sq := by
  have he : Even (n : ℤ) := by simpa using hn
  have hdiv : W.preΨ n ∣ W.Ψ₂Sq ^ 2 * (W.preΨ n).derivative ^ 2 -
      C ((n : k) ^ 2) * W.Φ n := by
    refine ⟨W.Ψ₂Sq ^ 2 * (W.preΨ n).derivative.derivative +
      W.Ψ₂Sq * W.invar * (W.preΨ n).derivative + 4 * W.Ψ₃ * W.preΨ n -
      C ((n : k) ^ 2) * X * W.preΨ n * W.Ψ₂Sq, ?_⟩
    simp only [divisionDifferentialDefect, divisionDifferential, ΨSq, ite_eq_left he,
      Int.cast_natCast] at hd
    linear_combination hd
  have h := W.isCoprime_preΨ_of_congr_Φ hchar hdiv
  simp only [pow_two] at h
  exact h.of_mul_right_left.of_mul_right_left

/-- The five-division polynomial of an elliptic curve is separable over
any field of characteristic different from five. -/
theorem separable_preΨ_five (h5 : (5 : k) ≠ 0) : (W.preΨ 5).Separable := by
  exact W.separable_preΨ_of_derivative_sq (n := 5) (by decide) h5
    (by simpa only [Nat.cast_ofNat] using W.preΨ_five_dvd_derivative_sq)

end WeierstrassCurve
