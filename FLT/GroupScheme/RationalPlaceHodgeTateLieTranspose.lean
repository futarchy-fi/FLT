/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateRealization
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Transposing the actual Cartier differential with its original Lie source

The target here is the dual of the Cartier Tate realization. Identifying its
cyclotomic twist with the original Tate realization requires perfect Tate
Cartier duality; this module does not assume or assert that identification.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 2000] Algebra.toModule Algebra.toSMul
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original Cartier differential extends over the full dual Tate realization. -/
def rationalPlaceHodgeTateDlogLinear :
    RationalPlaceTateRealization X.cartierDual →ₗ[ℂ_[p]] ℂ_[p] ⊗[O] X.cotangentLimit :=
  rationalPlaceComplexExtend (rationalPlaceHodgeTateDlog X)

/-- Extend the original Lie-cotangent evaluation pairing over C_p. -/
def rationalPlaceLieEvaluation :
    ℂ_[p] ⊗[O] X.IntegralTangent →ₗ[ℂ_[p]] Module.Dual ℂ_[p] (ℂ_[p] ⊗[O] X.cotangentLimit) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : ℂ_[p] →ₗ[ℂ_[p]] ℂ_[p]).smulRight (Module.Dual.baseChange ℂ_[p]))

/-- Scalar extension retains the original Lie evaluation on both pure tensors. -/
theorem rationalPlaceLieEvaluation_tmul (c b : ℂ_[p]) (d : X.IntegralTangent)
    (v : X.cotangentLimit) :
    rationalPlaceLieEvaluation X (c ⊗ₜ d) (b ⊗ₜ v) = c * (algebraMap O ℂ_[p] (d v) * b) := rfl

/-- Transpose the actual differential; the source is the original Lie module over C_p. -/
def rationalPlaceHodgeTateLieTranspose :
    ℂ_[p] ⊗[O] X.IntegralTangent →ₗ[ℂ_[p]]
      Module.Dual ℂ_[p] (RationalPlaceTateRealization X.cartierDual) :=
  (rationalPlaceHodgeTateDlogLinear X).dualMap.comp (rationalPlaceLieEvaluation X)

/-- The transposed map contracts the original Lie vector with the actual Cartier differential. -/
theorem rationalPlaceHodgeTateLieTranspose_pairing
    (v : ℂ_[p] ⊗[O] X.IntegralTangent) (c : ℂ_[p]) (y : X.CartierTate) :
    rationalPlaceHodgeTateLieTranspose X v (c ⊗ₜ y) =
      c • rationalPlaceLieEvaluation X v
        (TensorProduct.comm O _ ℂ_[p] (rationalPlaceHodgeTateDlog X y)) :=
  (rationalPlaceLieEvaluation X v).map_smul c _
end ThreeAdicPlan
