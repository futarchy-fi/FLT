/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Powers eliminate nilpotent discrepancies killed by an integer

A positive integer annihilating a nilpotent discrepancy suffices to equalize
positive powers, even in mixed characteristic. No assumption on the
characteristic of the whole ring is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentTorsionPowerEquality
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} {m : ℕ} {x y : R}

/-- Raising to an annihilating integer improves the discrepancy by one ideal power. -/
theorem power_step (hm : ∀ z ∈ I, (m : R) * z = 0) {k : ℕ} (hk : k ≠ 0)
    (h : x ≡ y [SMOD I ^ k]) : x ^ m ≡ y ^ m [SMOD I ^ (k + 1)] := by
  let J := I ⊔ Ideal.span {(m : R)}
  have hmJ : (m : R) ∈ J :=
    (show Ideal.span {(m : R)} ≤ J from le_sup_right) (Ideal.subset_span rfl)
  have hIJ : I ^ k ≤ J := (I.pow_le_self hk).trans le_sup_left
  have hz : I ^ k * Ideal.span {(m : R)} = ⊥ := by
    apply eq_bot_iff.mpr
    rw [mul_comm, Ideal.span_singleton_mul_le_iff]
    intro z hz
    exact hm z (I.pow_le_self hk hz)
  have he : I ^ k * J = I ^ (k + 1) := by
    change I ^ k * (I ⊔ Ideal.span {(m : R)}) = _
    rw [Ideal.mul_sup, hz, sup_bot_eq, pow_succ]
  rw [← he]
  exact h.pow_mul_of_le hmJ hIJ

/-- Iteration improves a discrepancy in `I` to the corresponding higher ideal power. -/
theorem power_iterate (hm : ∀ z ∈ I, (m : R) * z = 0)
    (h : x ≡ y [SMOD I]) (k : ℕ) :
    x ^ m ^ k ≡ y ^ m ^ k [SMOD I ^ (k + 1)] := by
  induction k with
  | zero => simpa only [pow_zero, Nat.zero_add, pow_one] using h
  | succ k ih =>
    simpa only [pow_succ m, pow_mul] using power_step hm (Nat.succ_ne_zero k) ih

/-- A nilpotent ideal killed by a positive integer admits a common equalizing power. -/
theorem exists_uniform_power (hm : 0 < m) (hI : IsNilpotent I)
    (hkill : ∀ z ∈ I, (m : R) * z = 0) :
    ∃ e : ℕ, 0 < e ∧ ∀ x y : R, x - y ∈ I → x ^ e = y ^ e := by
  obtain ⟨k, hk⟩ := hI
  refine ⟨m ^ k, pow_pos hm _, fun x y hxy => ?_⟩
  have h := power_iterate hkill (SModEq.sub_mem.mpr hxy) k
  have hz : I ^ (k + 1) = ⊥ := by rw [pow_succ, hk, zero_mul]; rfl
  rw [hz] at h
  exact SModEq.bot.mp h

/-- An integer-torsion nilpotent difference is killed by taking a positive power. -/
theorem exists_pos_pow_eq (hm : 0 < m) (hnil : IsNilpotent (x - y))
    (hkill : (m : R) * (x - y) = 0) : ∃ e : ℕ, 0 < e ∧ x ^ e = y ^ e := by
  let I : Ideal R := Ideal.span {x - y}
  have hI : IsNilpotent I := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    change (Ideal.span {x - y}) ^ k = 0
    rw [Ideal.span_singleton_pow, hk, Ideal.span_singleton_zero]
    rfl
  have hkillI : ∀ z ∈ I, (m : R) * z = 0 := by
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hz
    rw [← mul_assoc, hkill, zero_mul]
  obtain ⟨e, he, h⟩ := exists_uniform_power hm hI hkillI
  exact ⟨e, he, h x y (Ideal.subset_span rfl)⟩

end FLT.Mazur.NilpotentTorsionPowerEquality
