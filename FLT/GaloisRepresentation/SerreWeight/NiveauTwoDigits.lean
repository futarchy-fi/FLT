/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Tactic

/-!
# Normalizing the two base-p digits of a niveau-two exponent

Multiplication by p modulo p²−1 exchanges the two digits. A non-fixed
exponent therefore has a representative, up to this exchange, of the form
`a * (p + 1) + b` with `a < p - 1` and `1 ≤ b < p`.
-/

@[expose] public section
namespace GaloisRepresentation.SerreWeight

/-- Base-p digits of a reduced niveau-two exponent, excluding the pair (p−1,p−1). -/
theorem niveauTwo_digit_bounds {p e : ℕ} (hp : 1 < p) (he : e < p * p - 1) :
    e % p < p ∧ e / p < p ∧ e % p + p * (e / p) = e ∧
      e % p + e / p < 2 * (p - 1) := by
  have ha := Nat.mod_lt e (by omega : 0 < p)
  have hb : e / p < p := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have hd := Nat.mod_add_div e p
  have hn := Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)
  have hp' := Nat.sub_add_cancel (by omega : 1 ≤ p)
  refine ⟨ha, hb, hd, ?_⟩
  by_contra h
  have ha' : e % p = p - 1 := by omega
  have hb' : e / p = p - 1 := by omega
  rw [ha', hb'] at hd
  nlinarith

/-- Multiplication by p modulo p²−1 exchanges the two base-p digits. -/
theorem niveauTwo_frobenius_digits {p e : ℕ} (hp : 1 < p)
    (he : e < p * p - 1) :
    (p * e) % (p * p - 1) = e / p + p * (e % p) := by
  obtain ⟨ha, hb, hd, hs⟩ := niveauTwo_digit_bounds hp he
  have hn := Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)
  have hp' := Nat.sub_add_cancel (by omega : 1 ≤ p)
  have hbound : e / p + p * (e % p) < p * p - 1 := by
    by_cases h : e % p = p - 1
    · have hb' : e / p < p - 1 := by omega
      nlinarith
    · have ha' : e % p < p - 1 := by omega
      nlinarith
  have hid : p * e = (p * p - 1) * (e / p) + (e / p + p * (e % p)) := by
    nlinarith [congrArg (p * ·) hd]
  rw [hid, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hbound]

/-- Frobenius fixes precisely the exponents with equal base-p digits. -/
theorem niveauTwo_frobenius_fixed_iff {p e : ℕ} (hp : 1 < p)
    (he : e < p * p - 1) :
    (p * e) % (p * p - 1) = e ↔ e % p = e / p := by
  rw [niveauTwo_frobenius_digits hp he]
  have hd := (niveauTwo_digit_bounds hp he).2.2.1
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h] at hd ⊢
    exact hd

/-- An exponent outside niveau one has normalized digits after at most one Frobenius swap. -/
theorem exists_normalized_niveauTwo_digits {p e : ℕ} (hp : 1 < p)
    (he : e < p * p - 1) (hne : (p * e) % (p * p - 1) ≠ e) :
    ∃ a b : ℕ, a < p - 1 ∧ 1 ≤ b ∧ b < p ∧
      (e = a * (p + 1) + b ∨ (p * e) % (p * p - 1) = a * (p + 1) + b) := by
  obtain ⟨ha, hb, hd, _⟩ := niveauTwo_digit_bounds hp he
  have hne' : e % p ≠ e / p := mt (niveauTwo_frobenius_fixed_iff hp he).mpr hne
  rcases lt_or_gt_of_ne hne' with h | h
  · refine ⟨e % p, e / p - e % p, by omega, by omega,
      lt_of_le_of_lt (Nat.sub_le _ _) hb, Or.inr ?_⟩
    rw [niveauTwo_frobenius_digits hp he]
    have := Nat.sub_add_cancel (Nat.le_of_lt h)
    nlinarith
  · refine ⟨e / p, e % p - e / p, by omega, by omega,
      lt_of_le_of_lt (Nat.sub_le _ _) ha, Or.inl ?_⟩
    have := Nat.sub_add_cancel (Nat.le_of_lt h)
    nlinarith

end GaloisRepresentation.SerreWeight
