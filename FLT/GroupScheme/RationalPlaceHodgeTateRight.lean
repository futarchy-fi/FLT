/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceHodgeTateDlog
public import FLT.GroupScheme.PDivisibleCartierBidual

/-! # The right Hodge–Tate differential on the original Tate lattice

Double dual evaluation supplies the original Tate argument. The target is the
dual Lie module of the actual Cartier dual, with actual C_p coefficients.
This constructs the lattice map, without claiming surjectivity or exactness.
-/

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

/-- Finite freeness identifies the original cotangent with the dual of its integral Lie module. -/
def rationalPlaceCotangentLieDualEquiv :
    X.cotangentLimit ≃ₗ[O] Module.Dual O X.IntegralTangent := by
  let := rationalPlace_cotangentLimit_free X
  let := rationalPlace_cotangentLimit_finite X
  exact Module.evalEquiv O X.cotangentLimit

/-- The identification is evaluation, so it retains the original tangent pairing. -/
theorem rationalPlaceCotangentLieDualEquiv_apply (v : X.cotangentLimit)
    (d : X.IntegralTangent) : rationalPlaceCotangentLieDualEquiv X v d = d v := rfl

/-- The actual Cartier double dual gives the right differential on the original Tate lattice. -/
def rationalPlaceHodgeTateRightCotangent :
    X.tateSequences →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom]
      X.cartierDual.cotangentLimit ⊗[O] ℂ_[p] :=
  (rationalPlaceHodgeTateDlog X.cartierDual).comp X.cartierBidualTateMap

/-- The right lattice map has precisely the dual Lie target of the actual Cartier dual. -/
def rationalPlaceHodgeTateRight :
    X.tateSequences →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom]
      (Module.Dual O X.cartierDual.IntegralTangent) ⊗[O] ℂ_[p] :=
  (TensorProduct.congr (rationalPlaceCotangentLieDualEquiv X.cartierDual)
    (LinearEquiv.refl O ℂ_[p])).toLinearMap.comp (rationalPlaceHodgeTateRightCotangent X)
end ThreeAdicPlan
