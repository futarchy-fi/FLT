/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexRootSequenceShift
public import FLT.PadicHodgeTheory.ComplexCyclotomicPowerBounds

/-! # Integral coefficient bounds for actual compatible root powers -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]
  (s w : Perfection 𝓞_ℂ_[p] p) (a : ℕ → ℕ)
  (ha : ∀ n, w.val n = s.val n ^ a n)
include ha

/-- Original root equality gives a theta-ideal difference at every shifted level. -/
theorem complexRootPower_shift_sub_mem (n : ℕ) :
    WittVector.teichmuller p (complexRootSequenceShift p w n) -
      WittVector.teichmuller p (complexRootSequenceShift p s n) ^ a n ∈
        RingHom.ker (complexTheta p) := by
  change complexTheta p _ = 0
  rw [map_sub, map_pow, complexTheta_teichmuller, complexTheta_teichmuller,
    complexRootSequenceShift_sharp, complexRootSequenceShift_sharp, ha n, sub_self]

/-- The integral power error lies in prescribed p-adic and theta-adic precisions. -/
theorem complexRootPowerDifference_mem (k r n : ℕ) (hn : k + r ≤ n + 1) :
    WittVector.teichmuller p (complexRootSequenceShift p w 0) -
      WittVector.teichmuller p (complexRootSequenceShift p s 0) ^ a n ∈
        Ideal.span {(p : Ainf p)} ^ k ⊔ RingHom.ker (complexTheta p) ^ r := by
  have h := ideal_pow_iterated_sub_mem_sup (RingHom.ker (complexTheta p)) p k r n hn
    (complexRootPower_shift_sub_mem p s w a ha n)
  rw [← map_pow, complexRootSequenceShift_pow_prime_pow] at h
  have he : (WittVector.teichmuller p (complexRootSequenceShift p s n) ^ a n) ^ (p ^ n) =
      WittVector.teichmuller p (complexRootSequenceShift p s 0) ^ a n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← map_pow, complexRootSequenceShift_pow_prime_pow]
  rwa [he] at h

/-- In each actual integral theta quotient, the power error is arbitrarily p-divisible. -/
theorem complexRootPowerDifference_quotient_mem (k r n : ℕ) (hn : k + r ≤ n + 1) :
    Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexRootSequenceShift p w 0)) -
      Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexRootSequenceShift p s 0)) ^ a n ∈
        Ideal.span {(p : ComplexIntegralThetaQuotient p r)} ^ k := by
  let q := Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
  have h := Ideal.mem_map_of_mem q (complexRootPowerDifference_mem p s w a ha k r n hn)
  rw [Ideal.map_sup, Ideal.map_quotient_self] at h
  simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton,
    map_natCast, Ideal.map_quotient_self, sup_bot_eq, map_sub, map_pow] using h

end PadicHodgeTheory
