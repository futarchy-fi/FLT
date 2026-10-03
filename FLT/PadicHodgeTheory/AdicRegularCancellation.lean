/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Cancellation modulo powers from regularity modulo a parameter -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Regularity modulo r implies regularity modulo every power of r. -/
theorem adic_dvd_mul_cancel (r ξ : R) (hr : r ≠ 0)
    (hξ : ∀ a : R, r ∣ ξ * a → r ∣ a) (n : ℕ) (a : R) :
    r ^ n ∣ ξ * a ↔ r ^ n ∣ a := by
  constructor
  · induction n generalizing a with
    | zero => simp
    | succ n ih =>
      intro ha
      have hra : r ∣ a := hξ a ((dvd_pow_self r (Nat.succ_ne_zero n)).trans ha)
      obtain ⟨b, rfl⟩ := hra
      obtain ⟨c, hc⟩ := ha
      have hb : r ^ n ∣ ξ * b := by
        refine ⟨c, mul_left_cancel₀ hr ?_⟩
        calc r * (ξ * b) = ξ * (r * b) := by ring
             _ = r ^ (n + 1) * c := hc
             _ = r * (r ^ n * c) := by rw [pow_succ']; ring
      obtain ⟨d, hd⟩ := ih b hb
      exact ⟨d, by rw [hd, pow_succ', mul_assoc]⟩
  · exact fun h ↦ h.mul_left ξ

/-- Every power of a regular residue remains cancellable at every precision. -/
theorem adic_dvd_pow_mul_cancel (r ξ : R) (hr : r ≠ 0)
    (hξ : ∀ a : R, r ∣ ξ * a → r ∣ a) (k n : ℕ) (a : R) :
    r ^ n ∣ ξ ^ k * a ↔ r ^ n ∣ a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, adic_dvd_mul_cancel r ξ hr hξ, ih]

end PadicHodgeTheory
