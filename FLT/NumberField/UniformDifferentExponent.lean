/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.NumberField.Completion.UniformDifferentBound
public import FLT.NumberField.UnramifiedPrimeSupport
public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero

/-!
# A global degree bound for normalized different exponents

For a number field of degree at most `N`, every prime above a rational prime
has different exponent at most `(N+1)` times its ramification index.
This applies the local bound to the actual completed integer extension.
-/

@[expose] public noncomputable section

open IsDedekindDomain.HeightOneSpectrum

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace NumberField

variable (L : Type) [Field L] [NumberField L]

/-- Bounded global degree bounds the different exponent above every rational prime. -/
theorem differentExponentAt_le_degree_bound (N : ℕ) (hN : Module.finrank ℚ L ≤ N)
    (P : Ideal (𝓞 L)) [P.IsPrime] (q : ℕ) (hq : q.Prime) (hqP : (q : 𝓞 L) ∈ P) :
    differentExponentAt L P ≤ (N + 1) * P.ramificationIdx ℤ := by
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hqP
    exact hq.ne_zero hqP
  have : P.LiesOver (Ideal.span {(q : ℤ)}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top inferInstance)
      (Nat.prime_iff_prime_int.mp hq)).mpr (by simpa only [map_natCast] using hqP)
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  have : P.LiesOver v.asIdeal := ThreeAdicPlan.liesOver_ratPrime_of_liesOver_int P hq
  let w : v.Extension (𝓞 L) :=
    ⟨⟨P, inferInstance, hP⟩, IsDedekindDomain.HeightOneSpectrum.ext
      (Ideal.over_def P v.asIdeal).symm⟩
  have hmem := completion_prime_pow_mem_different L v w N hN
  have heq : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = q :=
    congrArg Subtype.val (ThreeAdicPlan.primesEquiv_ratPrime q hq)
  rw [heq] at hmem
  exact differentExponentAt_le_of_completion_mem L v w hq hmem

/-- In particular the field's own degree gives a uniform normalized exponent bound. -/
theorem differentExponentAt_le_degree (P : Ideal (𝓞 L)) [P.IsPrime]
    (q : ℕ) (hq : q.Prime) (hqP : (q : 𝓞 L) ∈ P) :
    differentExponentAt L P ≤ (Module.finrank ℚ L + 1) * P.ramificationIdx ℤ :=
  differentExponentAt_le_degree_bound L _ le_rfl P q hq hqP

end NumberField
