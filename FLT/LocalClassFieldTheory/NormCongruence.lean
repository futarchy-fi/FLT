/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormFirstOrder
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Congruence preservation by the norm

Reducing a multiplication matrix modulo a principal ideal shows that its
determinant, hence the norm, preserves the same congruence.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- Norms of congruent elements are congruent modulo the same base element. -/
theorem norm_sub_dvd_of_dvd (r : R) (x y : S)
    (h : algebraMap R S r ∣ x - y) : r ∣ Algebra.norm R x - Algebra.norm R y := by
  classical
  obtain ⟨z, hz⟩ := h
  have hxy : x = y + r • z := by
    rw [Algebra.smul_def]
    exact (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
  let b := Module.Free.chooseBasis R S
  let q := Ideal.Quotient.mk (Ideal.span {r})
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  change q (Algebra.norm R x) = q (Algebra.norm R y)
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b,
    RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  rw [hxy, map_add, map_smul]
  change q ((Algebra.leftMulMatrix b y) i j + r * (Algebra.leftMulMatrix b z) i j) = _
  rw [map_add, map_mul]
  have hr : q r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [hr, zero_mul, add_zero]
  rfl

/-- Norms preserve every power of a base element. -/
theorem norm_sub_pow_dvd (π : R) (n : ℕ) (x y : S)
    (h : (algebraMap R S π) ^ n ∣ x - y) :
    π ^ n ∣ Algebra.norm R x - Algebra.norm R y :=
  norm_sub_dvd_of_dvd R S (π ^ n) x y (by simpa only [map_pow] using h)

end LocalClassFieldTheory
