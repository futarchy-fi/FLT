/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Eliminating arbitrary-length cyclic power equations

Successive p-power equations determine a Frobenius-weighted coefficient
product. Closing the chain gives the root equation in degree p^r−1.
-/

@[expose] public section
namespace RaynaudParameters

variable {F : Type*} [CommGroupWithZero F]

/-- Eliminate a chain of p-power equations without dividing by any intermediate coordinate. -/
theorem coordinate_chain_power (p n : ℕ) (x a : ℕ → F)
    (h : ∀ i < n, x i ^ p = a i * x (i + 1)) :
    x 0 ^ (p ^ n) = (∏ i ∈ Finset.range n, a i ^ (p ^ (n - 1 - i))) * x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : (∏ i ∈ Finset.range n, a i ^ (p ^ (n - 1 - i))) ^ p =
        ∏ i ∈ Finset.range n, a i ^ (p ^ (n - i)) := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← pow_mul, ← pow_succ]
      congr 2
      have := Finset.mem_range.mp hi
      omega
    rw [pow_succ, pow_mul, ih (fun i hi ↦ h i (by omega)), mul_pow, h n (by omega), hw,
      Finset.prod_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_one]
    exact (mul_assoc _ _ _).symm

/-- Closing a nonzero chain gives the full higher-niveau root equation. -/
theorem coordinate_cycle_power (p r : ℕ) (hp : 1 ≤ p) (x a : ℕ → F)
    (hx : x 0 ≠ 0) (hcycle : x r = x 0)
    (h : ∀ i < r, x i ^ p = a i * x (i + 1)) :
    x 0 ^ (p ^ r - 1) = ∏ i ∈ Finset.range r, a i ^ (p ^ (r - 1 - i)) := by
  apply mul_right_cancel₀ hx
  rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)]
  rw [coordinate_chain_power p r x a h, hcycle]

end RaynaudParameters
