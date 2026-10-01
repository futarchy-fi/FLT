/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.Deformations.RepresentationTheory.TameTraceObstruction
public import Mathlib.Tactic

/-!
# Binary tame weights and the rank-two determinant

The scalar calculations after Raynaud's inertia-weight theorem: cyclotomic
determinant selects the two distinct binary digits, and a niveau-two generator
has norm of order p−1 and eigenvalue ratio of order p+1. In particular its norm
is a generator too, which is needed to use the cyclotomic self-twist detector.

These are conditional algebraic lemmas, not a finite-flat classification or a
construction of fundamental characters. Sources: Raynaud, §3.4, and Serre (1987), §2.
-/

@[expose] public section

namespace Representation

variable {k : Type*} [Field k] {z : kˣ} {p a b : ℕ}

/-- A nontrivial character value and its determinant select complementary binary digits. -/
theorem binary_digits_of_product (hz : z ≠ 1) (ha : a ≤ 1) (hb : b ≤ 1)
    (hdet : z ^ a * z ^ b = z) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · simp only [pow_zero, one_mul] at hdet
    exact (hz hdet.symm).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · simp only [pow_one] at hdet
    exact (hz (mul_left_cancel (hdet.trans (mul_one z).symm))).elim

/-- Ordinary inertia weights with cyclotomic determinant are 0 and 1. -/
theorem ordinary_digits (hp : 3 < p) (hz : orderOf z = p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hdet : z ^ a * z ^ b = z) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  apply binary_digits_of_product _ ha hb hdet
  intro he
  simp only [he, orderOf_one] at hz
  omega

/-- The norm of a niveau-two generator generates the niveau-one image. -/
theorem niveau_two_norm_order (hp : 1 < p) (hz : orderOf z = p * p - 1) :
    orderOf (z ^ (p + 1)) = p - 1 := by
  have hf : p * p - 1 = (p - 1) * (p + 1) := by
    have := Nat.sub_add_cancel (by omega : 1 ≤ p)
    have := Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)
    nlinarith
  rw [orderOf_pow_of_dvd (by omega : p + 1 ≠ 0)
    (by rw [hz, hf]; exact dvd_mul_left _ _), hz, hf, Nat.mul_div_left]
  omega

/-- The ratio of the two niveau-two eigenvalues has order p+1. -/
theorem niveau_two_ratio_order (hp : 1 < p) (hz : orderOf z = p * p - 1) :
    orderOf (z / z ^ p) = p + 1 := by
  have hf : p * p - 1 = (p + 1) * (p - 1) := by
    have := Nat.sub_add_cancel (by omega : 1 ≤ p)
    have := Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)
    nlinarith
  have he : z / z ^ p = (z ^ (p - 1))⁻¹ := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ p), pow_succ]
    simp [div_eq_mul_inv, mul_comm]
  rw [he, orderOf_inv, orderOf_pow_of_dvd (by omega : p - 1 ≠ 0)
    (by rw [hz, hf]; exact dvd_mul_left _ _), hz, hf, Nat.mul_div_left]
  omega

/-- The determinant of two Frobenius-conjugate binary weights selects 1 and p. -/
theorem niveau_two_digits (hp : 3 < p) (hz : orderOf z = p * p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1)
    (hdet : z ^ (a + p * b) * z ^ (p * a + b) = z ^ (p + 1)) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  have hn := niveau_two_norm_order (by omega : 1 < p) hz
  apply ordinary_digits hp hn ha hb
  calc
    (z ^ (p + 1)) ^ a * (z ^ (p + 1)) ^ b =
        z ^ (a + p * b) * z ^ (p * a + b) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ = z ^ (p + 1) := hdet

/-- The two ordinary eigenvalues have nonzero sum at a generator. -/
theorem ordinary_sum_ne_zero (hp : 3 < p) (hz : orderOf z = p - 1) :
    (1 : k) + (z : k) ≠ 0 := by
  apply add_ne_zero_of_orderOf_div_gt_two (1 : kˣ) z
  simpa only [one_div, orderOf_inv, hz] using (by omega : 2 < p - 1)

/-- The Frobenius-conjugate niveau-two eigenvalues have nonzero sum at a generator. -/
theorem niveau_two_sum_ne_zero (hp : 1 < p) (hz : orderOf z = p * p - 1) :
    (z : k) + ((z ^ p : kˣ) : k) ≠ 0 := by
  apply add_ne_zero_of_orderOf_div_gt_two z (z ^ p)
  rw [niveau_two_ratio_order hp hz]
  omega

end Representation
