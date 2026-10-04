/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # A bounded real-power budget for elementary Ax descent

The exponent `2 - 2/n` gives a deliberately nonoptimal uniform bound `p^2`.
At a degree drop from `n` to `k` with `2*k ≤ n`, it pays for the factor `p^(1/k)`.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory

/-- The degree budget is bounded independently of the positive degree. -/
def axDegreeFactor (p : ℕ) (n : ℕ) : ℝ := (p : ℝ) ^ (2 - 2 / (n : ℝ))

/-- Positive degrees have a budget at least one. -/
theorem axDegreeFactor_one_le {p n : ℕ} (hp : 1 ≤ p) (hn : 0 < n) :
    1 ≤ axDegreeFactor p n := by
  apply Real.one_le_rpow (by exact_mod_cast hp)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (2 : ℝ) / n ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith

/-- Increasing the degree increases the available budget. -/
theorem axDegreeFactor_mono {p m n : ℕ} (hp : 1 ≤ p) (hm : 0 < m) (hmn : m ≤ n) :
    axDegreeFactor p m ≤ axDegreeFactor p n := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp)
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by exact_mod_cast hm : (0 : ℝ) < m) (by exact_mod_cast hmn : (m : ℝ) ≤ n)
  linarith

/-- The budget is uniformly bounded by p squared. -/
theorem axDegreeFactor_le_sq {p n : ℕ} (hp : 1 ≤ p) : axDegreeFactor p n ≤ (p : ℝ) ^ 2 := by
  rw [axDegreeFactor, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp)
  have : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  norm_num
  linarith

/-- A halving of the degree pays for the p-adic binomial loss. -/
theorem axDegreeFactor_step {p k n : ℕ} (hp : 1 ≤ p) (hk : 0 < k) (hkn : 2 * k ≤ n) :
    axDegreeFactor p k * (p : ℝ) ^ (1 / (k : ℝ)) ≤ axDegreeFactor p n := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  rw [axDegreeFactor, axDegreeFactor, ← Real.rpow_add hp']
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hkn' : (2 : ℝ) * k ≤ n := by exact_mod_cast hkn
  have hdiv : (2 : ℝ) / n ≤ 1 / k := (div_le_div_iff₀ hn' hk').mpr (by linarith)
  simp only [div_eq_mul_inv, one_mul] at hdiv ⊢
  linarith

/-- The one-step root factor has kth power p. -/
theorem axRootFactor_pow {p k : ℕ} (hp : 0 < p) (hk : 0 < k) :
    ((p : ℝ) ^ (1 / (k : ℝ))) ^ k = p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    one_div_mul_cancel (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0), Real.rpow_one]

end PadicHodgeTheory
