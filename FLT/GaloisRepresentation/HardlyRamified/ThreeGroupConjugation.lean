/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# The tame conjugation obstruction in a three-group

The tame Frobenius relation at two conjugates inertia to its square.
In a three-group that relation forces the inertia element to be the identity.
This file proves the group-theoretic implication, independently of the local-field
construction of Frobenius and its relation with the tame character.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- Repeated conjugation iterates the exponent in a power-conjugation relation. -/
theorem conjugate_pow_of_conjugate_eq_pow {G : Type*} [Group G]
    (a b : G) (q : ℕ) (h : a * b * a⁻¹ = b ^ q) (n : ℕ) :
    a ^ n * b * (a ^ n)⁻¹ = b ^ (q ^ n) := by
  change MulAut.conj (a ^ n) b = b ^ (q ^ n)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_pow]
    change (a * b * a⁻¹) ^ (q ^ n) = _
    rw [h, ← pow_mul, pow_succ']

/-- An odd power of three makes `2^(3^n) - 1` prime to three. -/
theorem coprime_three_two_pow_three_pow_sub_one (n : ℕ) :
    Nat.Coprime 3 (2 ^ (3 ^ n) - 1) := by
  have hmod : 2 ^ (3 ^ n) % 3 = 2 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, pow_mul, Nat.pow_mod, ih]
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro h
  have hzero := Nat.mod_eq_zero_of_dvd h
  have hpos : 1 ≤ (2 : ℕ) ^ (3 ^ n) := Nat.one_le_pow _ _ (by decide)
  omega

/-- A squaring-conjugation relation is impossible for nontrivial three-power torsion
when the conjugating element also has three-power order. -/
theorem eq_one_of_three_power_conjugate_eq_sq {G : Type*} [Group G]
    (a b : G) (m n : ℕ) (ha : a ^ (3 ^ m) = 1) (hb : b ^ (3 ^ n) = 1)
    (h : a * b * a⁻¹ = b ^ 2) : b = 1 := by
  have hpow : b ^ (2 ^ (3 ^ m)) = b := by
    simpa only [ha, inv_one, one_mul, mul_one] using
      (conjugate_pow_of_conjugate_eq_pow a b 2 h (3 ^ m)).symm
  have hsub : b ^ (2 ^ (3 ^ m) - 1) = 1 := by
    have hle : 1 ≤ (2 : ℕ) ^ (3 ^ m) := Nat.one_le_pow _ _ (by decide)
    apply mul_left_cancel (a := b)
    rw [mul_one, ← pow_succ', Nat.sub_add_cancel hle, hpow]
  exact (pow_eq_one_iff_of_coprime
    ((coprime_three_two_pow_three_pow_sub_one m).pow_left n)).mp ⟨hb, hsub⟩

/-- In a three-group, an element conjugate to its square by another group element is trivial. -/
theorem IsPGroup.eq_one_of_conjugate_eq_sq {G : Type*} [Group G]
    (hG : IsPGroup 3 G) (a b : G) (h : a * b * a⁻¹ = b ^ 2) : b = 1 := by
  obtain ⟨m, hm⟩ := hG a
  obtain ⟨n, hn⟩ := hG b
  exact eq_one_of_three_power_conjugate_eq_sq a b m n hm hn h

end ThreeAdicPlan
