/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterDifferenceOperator
public import FLT.GroupScheme.RaynaudPowerCharacterOrthogonality

/-!
# Character differences are Hasse derivatives

For total degree at most q−1, character orthogonality kills every term
except the one whose removed exponent is the character weight.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (e : F →+* R)

/-- The coefficient of each term is selected by its removed exponent. -/
theorem power_monomialCoefficient (k m i : ℕ) (hk : 0 < k)
    (hkq : k ≤ Fintype.card Fˣ) (hmq : m ≤ Fintype.card Fˣ) (hi : i < m) :
    monomialCoefficient (embeddingCharacter e ^ k) e m i =
      if k = m - i then (m.choose i : R) else 0 := by
  classical
  unfold monomialCoefficient
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← mul_assoc,
    embedding_power_average e k (m - i) hk (by omega) hkq (by omega)]
  split_ifs <;> simp

/-- On the relevant degree range the difference is the Hasse derivative of its weight. -/
theorem step_power_monomial (k n : ℕ) (hk : 0 < k)
    (hkn : k + n ≤ Fintype.card Fˣ) :
    step (embeddingCharacter e ^ k) (fun a ↦ e a ^ (k + n)) =
      ((k + n).choose k : R) • (fun a ↦ e a ^ n) := by
  classical
  rw [step_monomial, Finset.sum_eq_single n]
  · rw [power_monomialCoefficient e k (k + n) n hk (by omega) hkn (by omega)]
    simp only [Nat.add_sub_cancel_right, ite_true]
    congr 1
    rw [← Nat.choose_symm (by omega : n ≤ k + n), Nat.add_sub_cancel_right]
  · intro i hi hne
    rw [power_monomialCoefficient e k (k + n) i hk (by omega) hkn
      (Finset.mem_range.mp hi), ite_eq_right (by omega), zero_smul]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

end ThreeAdicPlan.CharacterAverage
