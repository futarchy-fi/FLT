/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicApproximation
public import FLT.PadicHodgeTheory.ComplexThetaQuotientTopology
public import FLT.PadicHodgeTheory.IdealPowerDifference

/-! # Coefficient precision of actual cyclotomic power approximants -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual exponent error lies in a prescribed sum of p and theta powers. -/
theorem complexCyclotomicPowerDifference_mem (σ : PadicGalois p) (k r n : ℕ)
    (hn : k + r ≤ n + 1) :
    WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p)) -
      WittVector.teichmuller p (complexCyclotomicTilt p) ^ complexCyclotomicExponent p σ n ∈
        Ideal.span {(p : Ainf p)} ^ k ⊔ RingHom.ker (complexTheta p) ^ r := by
  have h := ideal_pow_iterated_sub_mem_sup (RingHom.ker (complexTheta p)) p k r n hn
    (complexCyclotomicApproximation_root_sub_mem p σ n)
  rwa [complexCyclotomicApproximation_galois_pow,
    complexCyclotomicApproximation_integer_pow] at h

/-- At each integral theta level the error is divisible by an arbitrarily large p-power. -/
theorem complexCyclotomicPowerDifference_quotient_mem (σ : PadicGalois p) (k r n : ℕ)
    (hn : k + r ≤ n + 1) :
    Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
      (WittVector.teichmuller p (complexTiltGalois p σ (complexCyclotomicTilt p))) -
      Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
        (WittVector.teichmuller p (complexCyclotomicTilt p)) ^
          complexCyclotomicExponent p σ n ∈
        Ideal.span {(p : ComplexIntegralThetaQuotient p r)} ^ k := by
  let q := Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ r)
  have h := Ideal.mem_map_of_mem q (complexCyclotomicPowerDifference_mem p σ k r n hn)
  rw [Ideal.map_sup, Ideal.map_quotient_self] at h
  simpa only [Ideal.map_pow, Ideal.map_span, Set.image_singleton,
    map_natCast, Ideal.map_quotient_self, sup_bot_eq, map_sub, map_pow] using h

end PadicHodgeTheory
