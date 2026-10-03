/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Span

/-! # A unit linear term preserves a principal adic parameter -/

@[expose] public noncomputable section
namespace PadicHodgeTheory

/-- Congruence to a parameter modulo its square makes two elements associated. -/
theorem associated_of_adic_linear_term {R : Type*} [CommRing R] (a b : R)
    [IsAdicComplete (Ideal.span {a}) R] (h : b - a ∈ Ideal.span {a} ^ 2) :
    Associated a b := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hu : IsUnit (1 + a * c) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    apply IsAdicComplete.le_jacobson_bot (Ideal.span {a})
    simpa only [add_sub_cancel_left] using
      (Ideal.mul_mem_right c (Ideal.span {a}) (Ideal.mem_span_singleton_self a))
  have hb : b = a * (1 + a * c) := by
    calc
      b = a + (b - a) := (add_sub_cancel a b).symm
      _ = a * (1 + a * c) := by rw [hc]; ring
  rw [hb]
  exact associated_mul_unit_right _ _ hu

/-- A nonzero nonunit in a domain does not belong to the square of its own ideal. -/
theorem notMem_square_span_self {R : Type*} [CommRing R] [IsDomain R]
    (a : R) (ha : a ≠ 0) (hu : ¬ IsUnit a) : a ∉ Ideal.span {a} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have he : 1 = a * c := mul_left_cancel₀ ha (by
    simpa only [pow_two, mul_assoc, mul_one] using hc)
  exact hu (IsUnit.of_mul_eq_one c he.symm)

end PadicHodgeTheory
