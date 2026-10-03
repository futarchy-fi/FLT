/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicPrincipalClosed
public import FLT.PadicHodgeTheory.ComplexCyclotomicPrincipal

/-! # Regularity and p-adic closedness of powers of the actual cyclotomic kernel -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The chosen prime tilt element is nonzero, as witnessed by its sharp. -/
theorem complexPrimeTilt_ne_zero : complexPrimeTilt p ≠ 0 := by
  intro h
  apply complexPrimeTilt_sharp_ne_zero p
  rw [h, ← complexTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

/-- The actual cyclotomic generator has nonzero reduction modulo p. -/
theorem complexCyclotomicKernel_coeff_zero_ne_zero :
    (complexCyclotomicKernel p).coeff 0 ≠ 0 := by
  have h := (complexCyclotomicKernel_associated p).map
    (WittVector.constantCoeff : Ainf p →+* IntegralTilt p)
  apply h.ne_zero_iff.mp
  change (complexThetaGenerator p).coeff 0 ≠ 0
  rw [complexThetaGenerator_coeff_zero]
  exact complexPrimeTilt_ne_zero p

/-- The actual generator is regular modulo p, proved in the integral tilt. -/
theorem complexCyclotomicKernel_regular_mod_prime (a : Ainf p)
    (ha : (p : Ainf p) ∣ complexCyclotomicKernel p * a) : (p : Ainf p) ∣ a := by
  rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero] at ha ⊢
  change WittVector.constantCoeff (complexCyclotomicKernel p * a) = 0 at ha
  rw [map_mul] at ha
  exact (mul_eq_zero.mp ha).resolve_left (complexCyclotomicKernel_coeff_zero_ne_zero p)

/-- All powers of the actual cyclotomic generator are regular at every p-adic precision. -/
theorem complexCyclotomicKernel_pow_cancel (k n : ℕ) (a : Ainf p) :
    (p : Ainf p) ^ n ∣ complexCyclotomicKernel p ^ k * a ↔ (p : Ainf p) ^ n ∣ a :=
  adic_dvd_pow_mul_cancel _ _ (WittVector.p_nonzero p (IntegralTilt p))
    (complexCyclotomicKernel_regular_mod_prime p) k n a

/-- Arbitrarily precise divisibility by xi^k implies actual divisibility in A_inf. -/
theorem complexCyclotomicKernel_pow_dvd_of_approximations (k : ℕ) (x : Ainf p)
    (hx : ∀ n : ℕ, ∃ a : Ainf p,
      (p : Ainf p) ^ n ∣ x - complexCyclotomicKernel p ^ k * a) :
    complexCyclotomicKernel p ^ k ∣ x := by
  apply dvd_of_adic_approximations (p : Ainf p) _
    (WittVector.p_nonzero p (IntegralTilt p)) _ x hx
  intro a ha
  simpa only [pow_one] using
    (complexCyclotomicKernel_pow_cancel p k 1 a).mp (by simpa only [pow_one] using ha)

/-- Every cyclotomic kernel power is closed for the p-adic topology. -/
theorem complexCyclotomicKernel_pow_isClosed (k : ℕ) [TopologicalSpace (Ainf p)]
    (hA : IsAdic (Ideal.span {(p : Ainf p)})) :
    IsClosed (Ideal.span {complexCyclotomicKernel p ^ k} : Set (Ainf p)) := by
  apply isClosed_span_of_adic_regular (p : Ainf p) _
    (WittVector.p_nonzero p (IntegralTilt p)) _ hA
  intro a ha
  simpa only [pow_one] using
    (complexCyclotomicKernel_pow_cancel p k 1 a).mp (by simpa only [pow_one] using ha)

end PadicHodgeTheory
