/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AdicFiniteFreeCoefficients
public import FLT.GroupScheme.PDivisibleCompletedDlogCoefficients
public import FLT.GroupScheme.PDivisibleIntegralTangentCoefficients
public import FLT.GroupScheme.RationalPlaceIntegralCoefficients

/-! # Actual completed cotangent coefficients at the original rational place -/

@[expose] public noncomputable section
open scoped TensorProduct
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual O_C is p-adically complete as a module over the original base. -/
theorem rationalPlaceComplexIntegers_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : O)}) 𝓞_ℂ_[p] := by
  apply (IsAdicComplete.map_algebraMap_iff (S := 𝓞_ℂ_[p]) (Ideal.span {(p : O)}) 𝓞_ℂ_[p]).mp
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  infer_instance

/-- The actual integral cotangent coefficient tensor is already complete. -/
theorem rationalPlaceCotangentTensor_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : O)}) (X.cotangentLimit ⊗[O] 𝓞_ℂ_[p]) := by
  let := rationalPlaceComplexIntegers_isAdicComplete (p := p)
  let := rationalPlace_cotangentLimit_free X
  let := rationalPlace_cotangentLimit_finite X
  exact AdicCompletion.finiteFree_tensor_isAdicComplete _

/-- Integral completion identifies with the tensor over actual complete coefficients. -/
def rationalPlaceCompletedCotangentEquiv :
    X.CompletedCotangentTensor (S := 𝓞_ℂ_[p]) ≃ₗ[O] X.cotangentLimit ⊗[O] 𝓞_ℂ_[p] := by
  let := rationalPlaceCotangentTensor_isAdicComplete X
  exact (AdicCompletion.ofLinearEquiv (Ideal.span {(p : O)}) _).symm

/-- The comparison inverts the specified integral completion map on every tensor. -/
theorem rationalPlaceCompletedCotangentEquiv_of (v : X.cotangentLimit ⊗[O] 𝓞_ℂ_[p]) :
    rationalPlaceCompletedCotangentEquiv X (AdicCompletion.of (Ideal.span {(p : O)}) _ v) = v := by
  let := rationalPlaceCotangentTensor_isAdicComplete X
  exact AdicCompletion.ofLinearEquiv_symm_of _ _
end ThreeAdicPlan
