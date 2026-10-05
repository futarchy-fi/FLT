/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.RationalRamificationBridge
public import FLT.NumberField.DifferentExponentBounds

/-!
# Rational unramifiedness and support of the absolute different

Unramifiedness outside a finite set of rational primes implies that every
prime factor of the absolute different contains a prime in that set.
-/

@[expose] public noncomputable section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K] (S : Finset ℕ)

/-- Translate rational-place unramifiedness to absolute unramifiedness over `ℤ`.
The zero prime is handled as well as the nonzero primes. -/
theorem isUnramifiedAt_int_of_unramifiedOutside
    (h : ∀ (q : ℕ) (hq : q.Prime), q ∉ S →
      Algebra.IsUnramifiedIn (𝓞 K) hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hS : ∀ q ∈ S, (q : 𝓞 K) ∉ P) :
    Algebra.IsUnramifiedAt ℤ P := by
  by_cases hP : P = ⊥
  · subst P
    apply not_dvd_differentIdeal_iff.mp
    simpa only [← Ideal.zero_eq_bot, zero_dvd_iff] using
      (differentIdeal_ne_bot : differentIdeal ℤ (𝓞 K) ≠ ⊥)
  have : NeZero P := ⟨hP⟩
  let q := Ideal.absNorm (P.under ℤ)
  have hq : q.Prime := Nat.absNorm_under_prime P
  have : P.LiesOver (Ideal.span {(q : ℤ)}) := Int.liesOver_span_absNorm P
  have hqmem : (q : 𝓞 K) ∈ P := by
    have hm := (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top inferInstance)
      (Nat.prime_iff_prime_int.mp hq)).mp
        (inferInstance : P.LiesOver (Ideal.span {(q : ℤ)}))
    simpa only [map_natCast] using hm
  have hqS : q ∉ S := fun hmem ↦ hS q hmem hqmem
  have : P.LiesOver hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
    ThreeAdicPlan.liesOver_ratPrime_of_liesOver_int P hq
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) P := h q hq hqS P inferInstance inferInstance
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv Rat.ringOfIntegersEquiv.symm.toIntAlgEquiv
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime P)

/-- All different exponents away from the specified rational primes vanish. -/
theorem differentExponentAt_eq_zero_of_unramifiedOutside
    (h : ∀ (q : ℕ) (hq : q.Prime), q ∉ S →
      Algebra.IsUnramifiedIn (𝓞 K) hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hS : ∀ q ∈ S, (q : 𝓞 K) ∉ P) :
    differentExponentAt K P = 0 :=
  differentExponentAt_eq_zero_of_isUnramifiedAt K P
    (isUnramifiedAt_int_of_unramifiedOutside K S h P hS)

/-- Every prime factor of the different lies above a prime from the exceptional set. -/
theorem exists_mem_of_mem_different_factors
    (h : ∀ (q : ℕ) (hq : q.Prime), q ∉ S →
      Algebra.IsUnramifiedIn (𝓞 K) hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    (P : Ideal (𝓞 K))
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 K))) :
    ∃ q ∈ S, (q : 𝓞 K) ∈ P := by
  classical
  have hp := (Ideal.mem_normalizedFactors_iff differentIdeal_ne_bot).mp hP
  have : P.IsPrime := hp.1
  by_contra! hn
  have hz := differentExponentAt_eq_zero_of_unramifiedOutside K S h P hn
  exact (Multiset.count_eq_zero.mp hz) hP

end NumberField
