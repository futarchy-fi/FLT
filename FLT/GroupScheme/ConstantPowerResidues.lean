/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.PrimePowerExact
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Tactic

/-! # Ordered maps of the constant cyclic p-power groups -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.ConstantPower
open GaloisRepresentation.PrimePower
variable (p : ℕ)

/-- Integer residues, including the trivial level zero. -/
abbrev Residue (n : ℕ) := Quot (p : ℤ) n

instance residueFinite [Fact p.Prime] (n : ℕ) : Finite (Residue p n) := by
  have : NeZero ((p : ℤ) ^ n) := ⟨pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)⟩
  infer_instance

/-- These constant groups have the required cardinality. -/
theorem residue_card (n : ℕ) : Nat.card (Residue p n) = p ^ n := by
  rw [Nat.card_congr (Int.quotientSpanEquivZMod ((p : ℤ) ^ n)).toEquiv, Nat.card_zmod]
  simp

/-- Inclusion multiplies integer representatives by the difference power. -/
def embed {m n : ℕ} (h : m ≤ n) : Residue p m →ₗ[ℤ] Residue p n :=
  (Ideal.span {(p : ℤ) ^ m}).mapQ _ ((p : ℤ) ^ (n - m) • LinearMap.id) (by
    intro x hx
    change (p : ℤ) ^ (n - m) * x ∈ Ideal.span {(p : ℤ) ^ n}
    rw [Ideal.mem_span_singleton] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_⟩
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h])

/-- Reduction keeps the same integer representative. -/
def reduce {m n : ℕ} (h : m ≤ n) : Residue p n →ₗ[ℤ] Residue p m :=
  (Ideal.span {(p : ℤ) ^ n}).mapQ _ LinearMap.id (by
    intro x hx
    exact (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ h)) hx)

@[simp] theorem embed_mk {m n : ℕ} (h : m ≤ n) (a : ℤ) :
    embed p h (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ((p : ℤ) ^ (n - m) * a) := rfl

@[simp] theorem reduce_mk {m n : ℕ} (h : m ≤ n) (a : ℤ) :
    reduce p h (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

/-- Ordered inclusions agree with the exact principal-power inclusion. -/
theorem embed_add (m n : ℕ) : embed p (Nat.le_add_right m n) = inclusion (p : ℤ) m n := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [embed_mk, inclusion_mk, Nat.add_sub_cancel_left]

/-- Ordered reductions agree with the exact principal-power reduction. -/
theorem reduce_add (m n : ℕ) : reduce p (Nat.le_add_left n m) = reduction (p : ℤ) m n := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Each ordered inclusion is injective. -/
theorem embed_injective [Fact p.Prime] {m n : ℕ} (h : m ≤ n) : Function.Injective (embed p h) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [embed_add]
  exact inclusion_injective (by exact_mod_cast (Fact.out : p.Prime).ne_zero) _ _

/-- Each ordered reduction is surjective. -/
theorem reduce_surjective {m n : ℕ} (h : m ≤ n) : Function.Surjective (reduce p h) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- Exactness uses the actual multiplication and reduction maps. -/
theorem residue_exact (m n : ℕ) :
    Function.Exact (embed p (Nat.le_add_right m n)) (reduce p (Nat.le_add_left n m)) := by
  rw [embed_add, reduce_add]
  exact GaloisRepresentation.PrimePower.exact _ _ _

/-- The level n group is killed by p^n. -/
theorem residue_killed (n : ℕ) (x : Residue p n) : p ^ n • x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simp only [nsmul_eq_mul, Nat.cast_pow]
  exact dvd_mul_right _ _

end ThreeAdicPlan.ConstantPower
