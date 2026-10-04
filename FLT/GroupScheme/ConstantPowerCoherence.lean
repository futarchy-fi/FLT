/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantPowerResidues

/-! # Coherence and multiplication in the constant residue tower -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.ConstantPower
variable (p : ℕ)

@[simp] theorem embed_refl (n : ℕ) (x : Residue p n) : embed p (le_refl n) x = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [embed_mk, Nat.sub_self, pow_zero, one_mul]

@[simp] theorem reduce_refl (n : ℕ) (x : Residue p n) : reduce p (le_refl n) x = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Ordered inclusions compose without changing the original representatives. -/
theorem embed_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (x : Residue p l) :
    embed p k (embed p h x) = embed p (h.trans k) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [embed_mk, ← mul_assoc, ← pow_add, Nat.sub_add_sub_cancel k h]

/-- Ordered reductions compose. -/
theorem reduce_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (x : Residue p n) :
    reduce p h (reduce p k x) = reduce p (h.trans k) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Reducing after inclusion is multiplication at the lower level. -/
theorem reduce_embed {m n : ℕ} (h : m ≤ n) (x : Residue p m) :
    reduce p h (embed p h x) = p ^ (n - m) • x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [embed_mk, reduce_mk]
  simp only [nsmul_eq_mul, Nat.cast_pow, map_mul, map_pow, map_natCast]

/-- Including after reduction is multiplication at the higher level. -/
theorem embed_reduce {m n : ℕ} (h : m ≤ n) (x : Residue p n) :
    embed p h (reduce p h x) = p ^ (n - m) • x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [reduce_mk, embed_mk]
  simp only [nsmul_eq_mul, Nat.cast_pow, map_mul, map_pow, map_natCast]

end ThreeAdicPlan.ConstantPower
