/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exact sequences between principal power quotients

Multiplication by `a^n` and reduction give the coefficient exact sequence
`R/(a^m) → R/(a^(m+n)) → R/(a^n)`. Over a domain the first map is injective
when `a ≠ 0`. These are the coefficient maps for a torsion-level tower;
no integral group-scheme model or compatibility of such models is asserted.
-/

@[expose] public section

namespace GaloisRepresentation.PrimePower

variable {R : Type*} [CommRing R]

/-- The quotient by a principal power ideal. -/
abbrev Quot (a : R) (n : ℕ) := R ⧸ Ideal.span {a ^ n}

/-- Multiplication by `a^n` on representatives. -/
def inclusion (a : R) (m n : ℕ) : Quot a m →ₗ[R] Quot a (m + n) :=
  (Ideal.span {a ^ m}).mapQ (Ideal.span {a ^ (m + n)})
    (a ^ n • LinearMap.id) (by
      intro x hx
      change a ^ n * x ∈ Ideal.span {a ^ (m + n)}
      rw [Ideal.mem_span_singleton] at hx ⊢
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, by ring⟩)

/-- Reduction from level `m+n` to level `n`. -/
def reduction (a : R) (m n : ℕ) : Quot a (m + n) →ₗ[R] Quot a n :=
  (Ideal.span {a ^ (m + n)}).mapQ (Ideal.span {a ^ n}) LinearMap.id (by
    intro x hx
    change x ∈ Ideal.span {a ^ n}
    rw [Ideal.mem_span_singleton] at hx ⊢
    exact (show a ^ n ∣ a ^ (m + n) by
      rw [pow_add]
      exact dvd_mul_left _ _).trans hx)

@[simp]
lemma inclusion_mk (a : R) (m n : ℕ) (x : R) :
    inclusion a m n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (a ^ n * x) := rfl

@[simp]
lemma reduction_mk (a : R) (m n : ℕ) (x : R) :
    reduction a m n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

/-- Every lower-level residue has a lift. -/
theorem reduction_surjective (a : R) (m n : ℕ) :
    Function.Surjective (reduction a m n) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-- The kernel of reduction consists exactly of the scaled lower-level residues. -/
theorem exact (a : R) (m n : ℕ) :
    Function.Exact (inclusion a m n) (reduction a m n) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    rw [reduction_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hy, inclusion_mk, reduction_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact dvd_mul_right _ _

/-- A nonzero principal power gives an injective map of torsion levels over a domain. -/
theorem inclusion_injective [IsDomain R] {a : R} (ha : a ≠ 0) (m n : ℕ) :
    Function.Injective (inclusion a m n) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change inclusion a m n (Ideal.Quotient.mk _ x) = 0 at hx
  rw [inclusion_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  have hxy : x = a ^ m * y := by
    apply mul_left_cancel₀ (pow_ne_zero n ha)
    rw [hy, pow_add]
    ring
  change Ideal.Quotient.mk (Ideal.span {a ^ m}) x = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hxy]
  exact dvd_mul_right _ _

end GaloisRepresentation.PrimePower
