/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTateGalois
public import FLT.GroupScheme.PDivisibleIntegralTangentCoefficients

/-! # The dual system and its integral coefficient pairing at the original rational place -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Cartier duality is constructed over the original rational-place completion. -/
def rationalPlaceCartierSystem :
    PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height := X.cartierDual

/-- The cotangent of this actual integral dual system is finite free. -/
theorem rationalPlaceCartier_cotangent_free :
    Module.Free ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      X.cartierDual.cotangentLimit :=
  X.cartierDual.cotangentLimit_free (rationalPlaceIntegersEquiv p).toRingEquiv

variable {M : Type} [AddCommGroup M]
  [Module ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) M]

/-- Extend coefficients in the integral tangent of the actual dual local system. -/
def rationalPlaceCartierIntegralCoefficients :
    X.cartierDual.IntegralTangent ⊗[
      (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] M ≃ₗ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      (X.cartierDual.cotangentLimit →ₗ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] M) :=
  X.cartierDual.integralTangentCoefficientsEquiv (rationalPlaceIntegersEquiv p).toRingEquiv

/-- The dual coefficient comparison retains the actual integral evaluation pairing. -/
theorem rationalPlaceCartierIntegralCoefficients_pairing
    (d : X.cartierDual.IntegralTangent) (a : M) (z : X.cartierDual.cotangentLimit) :
    rationalPlaceCartierIntegralCoefficients X (d ⊗ₜ a) z =
      X.cartierDual.integralTangentPairing d z • a := rfl

/-- At each original dual level, p-power torsion coefficients give the same limit evaluation. -/
theorem rationalPlaceCartierLevelCoefficients_pairing (n : ℕ)
    (hM : ∀ a : M, p ^ n • a = 0)
    (d : X.cartierDual.IntegralTangent) (a : M) (z : X.cartierDual.cotangentLimit) :
    X.cartierDual.integralTangentLevelCoefficientsEquiv
      (rationalPlaceIntegersEquiv p).toRingEquiv n hM (d ⊗ₜ a)
        (X.cartierDual.cotangentEval n z) = X.cartierDual.integralTangentPairing d z • a :=
  X.cartierDual.integralTangentLevelCoefficientsEquiv_pairing
    (rationalPlaceIntegersEquiv p).toRingEquiv n hM d a z

end ThreeAdicPlan
