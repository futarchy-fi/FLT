/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicTame

/-!
# The rational prime is a normalized uniformizer

The p-adic integer comparison gives irreducibility. Association with the
normalized tame uniformizer then determines its original valuation.
-/

@[expose] public noncomputable section
namespace LocalCyclotomic
open IsLocalRing NumberField

variable (p : ℕ) [Fact p.Prime]
local notation "v" => rationalPlace p
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v

/-- The prime is irreducible in the original rational completion integers. -/
theorem rationalPrime_irreducible : Irreducible (p : O) := by
  let e : ℤ_[p] ≃+* O :=
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  simpa only [map_natCast] using (MulEquiv.irreducible_iff (f := e)).mpr PadicInt.irreducible_p

/-- The rational prime has the same normalized valuation as the chosen uniformizer. -/
theorem rationalPrime_valuation :
    Valued.v (p : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  have hassoc : Associated (tameUniformizer v) (p : O) :=
    Ideal.span_singleton_eq_span_singleton.mp <|
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
        ℚ v (tameUniformizer_spec v)).symm.trans (rationalPrime_irreducible p).maximalIdeal_eq
  obtain ⟨u, hu⟩ := hassoc
  have hv : Valued.v (u : O).1 = 1 :=
    (ValuationSubring.isUnit_iff_valued_eq_one (u : O)).mp u.isUnit
  have h := congrArg (fun x : O ↦ Valued.v x.1) hu
  simpa only [MulMemClass.coe_mul, Valuation.map_mul, tameUniformizer_spec, hv, mul_one,
    SubringClass.coe_natCast] using h.symm

end LocalCyclotomic
