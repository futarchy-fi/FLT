/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicRegular

/-! # Separated integral quotients by powers of the actual Fontaine theta kernel -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The n-th actual integral theta quotient, including the zero quotient at n = 0. -/
abbrev ComplexIntegralThetaQuotient (n : ℕ) :=
  Ainf p ⧸ RingHom.ker (complexTheta p) ^ n

/-- Powers of the actual theta kernel have the explicit cyclotomic generator. -/
theorem complexTheta_ker_pow_eq_span (n : ℕ) :
    RingHom.ker (complexTheta p) ^ n = Ideal.span {complexCyclotomicKernel p ^ n} := by
  rw [complexCyclotomicKernel_ker_eq_span, Ideal.span_singleton_pow]

/-- The actual kernel powers are closed in the p-adic topology on A_inf. -/
theorem complexTheta_ker_pow_isClosed (n : ℕ) [TopologicalSpace (Ainf p)]
    (hA : IsAdic (Ideal.span {(p : Ainf p)})) :
    IsClosed ((RingHom.ker (complexTheta p) ^ n : Ideal (Ainf p)) : Set (Ainf p)) := by
  rw [complexTheta_ker_pow_eq_span]
  exact complexCyclotomicKernel_pow_isClosed p n hA

/-- An element divisible by every p-power is zero in each integral theta quotient. -/
theorem complexIntegralThetaQuotient_eq_zero (n : ℕ) (x : ComplexIntegralThetaQuotient p n)
    (hx : ∀ k : ℕ, (p : ComplexIntegralThetaQuotient p n) ^ k ∣ x) : x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem, complexTheta_ker_pow_eq_span,
    Ideal.mem_span_singleton]
  apply complexCyclotomicKernel_pow_dvd_of_approximations p n x
  intro k
  obtain ⟨b, hb⟩ := hx k
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : x - (p : Ainf p) ^ k * b ∈ RingHom.ker (complexTheta p) ^ n := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] using hb
  rw [complexTheta_ker_pow_eq_span, Ideal.mem_span_singleton] at he
  obtain ⟨a, ha⟩ := he
  refine ⟨a, b, ?_⟩
  rw [← ha]
  ring

/-- Separatedness is proved for every actual quotient; it is not a supplied instance. -/
instance complexIntegralThetaQuotient_isHausdorff (n : ℕ) :
    IsHausdorff (Ideal.span {(p : ComplexIntegralThetaQuotient p n)})
      (ComplexIntegralThetaQuotient p n) where
  haus' x hx := complexIntegralThetaQuotient_eq_zero p n x fun k ↦ by
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using hx k

/-- Multiplication by p is injective on every integral theta quotient. -/
theorem complexIntegralThetaQuotient_prime_mul_eq_zero (n : ℕ)
    (x : ComplexIntegralThetaQuotient p n) (hx : (p : ComplexIntegralThetaQuotient p n) * x = 0) :
    x = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : (p : Ainf p) * x ∈ RingHom.ker (complexTheta p) ^ n := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_natCast] using hx
  rw [complexTheta_ker_pow_eq_span, Ideal.mem_span_singleton] at he
  obtain ⟨b, hb⟩ := he
  have hd : (p : Ainf p) ∣ b := by
    have h := (complexCyclotomicKernel_pow_cancel p n 1 b).mp
      (by simpa only [pow_one, ← hb] using dvd_mul_right (p : Ainf p) x)
    simpa only [pow_one] using h
  obtain ⟨c, rfl⟩ := hd
  rw [Ideal.Quotient.eq_zero_iff_mem, complexTheta_ker_pow_eq_span,
    Ideal.mem_span_singleton]
  refine ⟨c, mul_left_cancel₀ (WittVector.p_nonzero p (IntegralTilt p)) ?_⟩
  rw [hb]
  ring

end PadicHodgeTheory
