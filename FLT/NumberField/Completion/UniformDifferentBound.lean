/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.CompletionIntegersAdic
public import FLT.Mathlib.NumberTheory.Padics.DifferentBoundEquiv
public import FLT.NumberField.Completion.RankBound

/-!
# Uniform different bounds for actual number-field completions

Henselianity and the integral rank bound are proved for the full completed
integer ring. No choice of a monogenic order or totally ramified subfield is needed.
-/

@[expose] public noncomputable section

open IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace NumberField

variable (L : Type) [Field L] [NumberField L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 L))

/-- The rational prime to the global degree plus one belongs to the full local different. -/
theorem completion_prime_pow_mem_different (N : ℕ) (hN : Module.finrank ℚ L ≤ N) :
    ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : w.1.adicCompletionIntegers L) ^ (N + 1) ∈
      differentIdeal (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let : HenselianLocalRing (w.1.adicCompletionIntegers L) :=
    LocalRoot.completionIntegers_henselian w.1
  let : IsScalarTower (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  let : FaithfulSMul (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) :=
    FaithfulSMul.of_field_isFractionRing _ _ (v.adicCompletion ℚ) (w.1.adicCompletion L)
  exact IsDiscreteValuationRing.prime_pow_mem_different_of_base_equiv
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv N
    ((completionIntegers_finrank_le_global L v w).trans hN)

/-- Containment in a completed different bounds the corresponding global exponent. -/
theorem differentExponentAt_le_of_completion_mem {q n : ℕ} (hq : q.Prime)
    [w.1.asIdeal.LiesOver (Ideal.span {(q : ℤ)})]
    (hmem : (q : w.1.adicCompletionIntegers L) ^ n ∈
      differentIdeal (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)) :
    differentExponentAt L w.1.asIdeal ≤ n * w.1.asIdeal.ramificationIdx ℤ := by
  classical
  have hqne : Ideal.span {(q : w.1.adicCompletionIntegers L)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hq.ne_zero
  have hd : differentIdeal (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr hq.ne_zero) hmem
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hd
    (pow_ne_zero n hqne)).mp (Ideal.dvd_iff_le.mpr
      (show Ideal.span {(q : w.1.adicCompletionIntegers L)} ^ n ≤ _ by
        rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
        exact hmem))
  have hcount := Multiset.count_le_of_le (w.1.completionIdeal L) hle
  rw [count_differentIdeal_completion, normalizedFactors_pow, Multiset.count_nsmul] at hcount
  have hqcount := w.1.count_normalizedFactors_map_completion L (Ideal.span {(q : 𝓞 L)})
  simp only [Ideal.map_span, Set.image_singleton, map_natCast] at hqcount
  rw [hqcount, count_normalizedFactors_span_prime_eq_ramificationIdx L w.1.asIdeal q hq]
    at hcount
  exact hcount

end NumberField
