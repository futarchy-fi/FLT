/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCoefficientGalois
public import FLT.GroupScheme.PDivisibleCartierDlogLimit

/-! # Equivariance of the original finite integral Cartier differentials -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
  (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- Specializing original integral point coordinates intertwines the actual Galois action. -/
theorem rationalPlaceCartierCoordinate_galois (n : ℕ) (y : X.CartierTate) :
    (rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)).comp
      ((rationalPlaceIntegralCoefficients p).comp (X.cartierTateIntegralCoordinate n y)) =
    (rationalPlaceIntegralCoefficients p).comp (X.cartierTateIntegralCoordinate n (σ • y)) := by
  apply AlgHom.ext
  intro a
  apply rationalPlaceIntegralCoefficients_galois
  change (X.level n).cartierDual.pointCoordinate (σ • X.cartierTateEval n y) (1 ⊗ₜ a) = _
  rw [FF.pointCoordinate_smul]
  rfl

/-- The actual finite dlog tensor is equivariant, with Galois acting on its coefficients. -/
theorem rationalPlaceCartierDlogAt_galois (n : ℕ) (y : X.CartierTate) :
    (rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
      (X.cartierTateDlogAt (rationalPlaceIntegralCoefficients p) n y) =
    X.cartierTateDlogAt (rationalPlaceIntegralCoefficients p) n (σ • y) := by
  unfold PDivisibleSystem.cartierTateDlogAt FF.cartierDlog
  rw [HopfAlgebra.CartierDual.testDlog_coefficients, rationalPlaceCartierCoordinate_galois]
end ThreeAdicPlan
