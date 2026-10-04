/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCotangentComplete
public import FLT.GroupScheme.PDivisibleCotangentFiniteSets
public import FLT.GroupScheme.PDivisibleIntegralTangent
public import FLT.GroupScheme.PDivisibleTangentReduction

/-! # Cotangent reduction and algebraic tangents at the original rational place -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Reduction at the original rational place uses the actual evaluation, without extra premises. -/
def rationalPlaceCotangentReductionEquiv (n : ℕ) :
    (X.cotangentLimit ⧸ LinearMap.range
      (p ^ n • (LinearMap.id : X.cotangentLimit →ₗ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] _))) ≃ₗ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ] X.LevelCotangent n := by
  let (k : ℕ) : Finite (X.LevelCotangent k) := rationalPlace_levelCotangent_finite X k
  exact X.cotangentReductionEquiv n

/-- The rational-place reduction retains the original projection on every representative. -/
theorem rationalPlaceCotangentReductionEquiv_mk (n : ℕ) (x : X.cotangentLimit) :
    rationalPlaceCotangentReductionEquiv X n (Submodule.Quotient.mk x) =
      X.cotangentEval n x := rfl

/-- The original rational-place cotangent limit is complete for its p-adic filtration. -/
theorem rationalPlace_cotangentLimit_isAdicComplete :
    IsAdicComplete (Ideal.span {(p :
      (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)}) X.cotangentLimit := by
  let (k : ℕ) : Finite (X.LevelCotangent k) := rationalPlace_levelCotangent_finite X k
  exact X.cotangentLimit_isAdicComplete

/-- The original rational-place integral algebraic tangent is finite. -/
theorem rationalPlace_integralTangent_finite :
    Module.Finite ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      X.IntegralTangent := X.integralTangent_finite (rationalPlaceIntegersEquiv p).toRingEquiv

/-- Its algebraic tangent dual is free over the original discrete valuation ring. -/
theorem rationalPlace_integralTangent_free :
    Module.Free ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      X.IntegralTangent := X.integralTangent_free (rationalPlaceIntegersEquiv p).toRingEquiv

end ThreeAdicPlan
