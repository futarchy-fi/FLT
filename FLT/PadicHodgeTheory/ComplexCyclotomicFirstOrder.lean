/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegralThickening
public import FLT.PadicHodgeTheory.ComplexCyclotomicRegular

/-! # Nonvanishing of the integral first-order cyclotomic system -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual cyclotomic difference at integral first-order precision. -/
def complexCyclotomicFirstOrder (s : ℕ) : ComplexIntegralThickening p 2 s :=
  Ideal.Quotient.mk _ (complexCyclotomicDifference p)

/-- First-order precision reduction retains the same original difference. -/
theorem complexCyclotomicFirstOrder_reduce {s t : ℕ} (h : s ≤ t) :
    complexThickeningReduce p (le_refl 2) h (complexCyclotomicFirstOrder p t) =
      complexCyclotomicFirstOrder p s := rfl

/-- The integral cyclotomic difference does not lie in the square of the theta kernel. -/
theorem complexCyclotomicDifference_notMem_ker_square :
    complexCyclotomicDifference p ∉ RingHom.ker (complexTheta p) ^ 2 := by
  rw [complexCyclotomicKernel_ker_eq_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  rw [complexCyclotomicDifference_factor, pow_two] at h
  have hd := (mul_dvd_mul_iff_left (complexCyclotomicKernel_ne_zero p)).mp h
  obtain ⟨a, ha⟩ := hd
  have hz : complexTheta p (complexCyclotomicShiftDifference p) = 0 := by
    rw [ha, map_mul]
    have hk := complexCyclotomicKernel_mem_ker p
    change complexTheta p (complexCyclotomicKernel p) = 0 at hk
    rw [hk, zero_mul]
  rw [complexCyclotomicShiftDifference_theta, sub_eq_zero] at hz
  exact (complexCyclotomicRoot_primitive p).ne_one (Fact.out : p.Prime).one_lt hz

/-- Some finite p-adic precision detects the nonzero integral first-order period.
This does not assert nonvanishing at every precision. -/
theorem complexCyclotomicFirstOrder_exists_ne_zero :
    ∃ s : ℕ, complexCyclotomicFirstOrder p s ≠ 0 := by
  by_contra h
  push Not at h
  apply complexCyclotomicDifference_notMem_ker_square p
  rw [complexCyclotomicKernel_ker_eq_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  apply complexCyclotomicKernel_pow_dvd_of_approximations p 2
  intro s
  have hs := h s
  rw [complexCyclotomicFirstOrder, Ideal.Quotient.eq_zero_iff_mem,
    complexThickeningIdeal, complexCyclotomicKernel_ker_eq_span,
    Ideal.span_singleton_pow, Submodule.mem_sup] at hs
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨c, ?_⟩
  rw [← hab, add_sub_cancel_left]
  exact Ideal.mem_span_singleton.mp hb

/-- Precision zero is trivial, so a detecting precision is positive. -/
theorem complexCyclotomicFirstOrder_exists_pos :
    ∃ s : ℕ, 0 < s ∧ complexCyclotomicFirstOrder p s ≠ 0 := by
  obtain ⟨s, hs⟩ := complexCyclotomicFirstOrder_exists_ne_zero p
  refine ⟨s, ?_, hs⟩
  by_contra hz
  have he : s = 0 := by omega
  subst s
  apply hs
  rw [complexCyclotomicFirstOrder, Ideal.Quotient.eq_zero_iff_mem]
  simp [complexThickeningIdeal]

end PadicHodgeTheory
