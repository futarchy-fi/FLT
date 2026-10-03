/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterDifferenceOperator

/-!
# Factorial values for embedding characters

The finite-difference operator is triangular on monomials, with diagonal
coefficient equal to the degree. Its n-fold application to degree n is n!.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (χ : Fˣ →* Rˣ) (e : F →+* R)

/-- More differences than the monomial degree give zero. -/
theorem step_pow_monomial_eq_zero (n m : ℕ) (hm : m < n) :
    (step χ ^ n) (fun a ↦ e a ^ m) = 0 := by
  induction n generalizing m with
  | zero => omega
  | succ n hn =>
    rw [pow_succ, Module.End.mul_apply, step_monomial, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul, hn i (by have := Finset.mem_range.mp hi; omega), smul_zero]

/-- The n-fold difference of a degree-n monomial is n factorial. -/
theorem step_pow_monomial_eq_factorial
    (he : ∀ u : Fˣ, (χ u : R) = e u) (n : ℕ) :
    (step χ ^ n) (fun a ↦ e a ^ n) = fun _ ↦ (n.factorial : R) := by
  induction n with
  | zero => ext a; simp
  | succ n hn =>
    rw [pow_succ, Module.End.mul_apply, step_monomial, map_sum, Finset.sum_range_succ]
    have hz : ∑ i ∈ Finset.range n,
        (step χ ^ n) (monomialCoefficient χ e (n + 1) i • (fun a ↦ e a ^ i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [map_smul, step_pow_monomial_eq_zero χ e n i (Finset.mem_range.mp hi), smul_zero]
    rw [hz, zero_add, map_smul, hn, monomialCoefficient_top χ e he]
    ext a
    simp [Nat.factorial_succ]

omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- Positive powers of an embedding character extend by zero to the corresponding monomial. -/
theorem value_pow_embedding (he : ∀ u : Fˣ, (χ u : R) = e u)
    (n : ℕ) (hn : n ≠ 0) (a : F) : value (χ ^ n) a = e a ^ n := by
  classical
  by_cases ha : a = 0
  · simp [ha, hn]
  · simp only [value, dite_eq_right ha, MonoidHom.pow_apply, Units.val_pow_eq_pow_val,
      he, Units.val_mk0]

/-- The universal constant for n repetitions of an embedding character is n factorial. -/
theorem constant_embedding_factorial (he : ∀ u : Fˣ, (χ u : R) = e u)
    (n : ℕ) (hn : n ≠ 0) : constant χ (χ ^ n) n = (n.factorial : R) := by
  unfold constant
  rw [show value (χ ^ n) = (fun a ↦ e a ^ n) from funext (value_pow_embedding χ e he n hn)]
  rw [iterate_eq_step_pow, step_pow_monomial_eq_factorial χ e he]

end ThreeAdicPlan.CharacterAverage
