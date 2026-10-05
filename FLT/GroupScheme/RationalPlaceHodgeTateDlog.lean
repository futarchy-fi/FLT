/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCompletedCotangent
public import FLT.GroupScheme.RationalPlaceComplexCoefficients
public import FLT.GroupScheme.PDivisibleCartierDlogLinearity

/-! # The original Cartier Tate differential over actual complete coefficients

This constructs the integral differential and its C_p specialization. Exactness
and the other Hodge–Tate map require separate proofs.
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

/-- The original dual Tate differential lands in the actual integral cotangent tensor. -/
def rationalPlaceHodgeTateDlogIntegral :
    X.CartierTate →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom]
      X.cotangentLimit ⊗[O] 𝓞_ℂ_[p] := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := rationalPlace_levelCotangent_finite X n
  exact (rationalPlaceCompletedCotangentEquiv X).toLinearMap.comp
    (X.cartierTateCompletedDlogLinear (rationalPlaceIntegersEquiv p).toRingEquiv
      (rationalPlaceIntegralCoefficients p))

/-- The integral map retains every finite original Cartier differential. -/
theorem rationalPlaceHodgeTateDlogIntegral_eval (y : X.CartierTate) (n : ℕ) :
    (X.cotangentEval n).rTensor 𝓞_ℂ_[p] (rationalPlaceHodgeTateDlogIntegral X y) =
      X.cartierTateDlogAt (rationalPlaceIntegralCoefficients p) n y := by
  let (k : ℕ) : Finite (X.LevelCotangent k) := rationalPlace_levelCotangent_finite X k
  have h := X.cotangentTensorCompletionEquiv_of (rationalPlaceHodgeTateDlogIntegral X y) n
  have he : AdicCompletion.of (Ideal.span {(p : O)}) _ (rationalPlaceHodgeTateDlogIntegral X y) =
      X.cartierTateCompletedDlog (rationalPlaceIntegralCoefficients p) y := by
    apply (rationalPlaceCompletedCotangentEquiv X).injective
    rw [rationalPlaceCompletedCotangentEquiv_of]
    rfl
  rw [he] at h
  exact h.symm.trans (X.cartierTateCompletedDlog_eval (rationalPlaceIntegralCoefficients p) y n)

/-- Invert p only after taking the integral completed Cartier differential. -/
def rationalPlaceHodgeTateDlog :
    X.CartierTate →ₛₗ[(rationalPlaceIntegersEquiv p).symm.toRingHom]
      X.cotangentLimit ⊗[O] ℂ_[p] :=
  ((IsScalarTower.toAlgHom O 𝓞_ℂ_[p] ℂ_[p]).toLinearMap.lTensor X.cotangentLimit).comp
    (rationalPlaceHodgeTateDlogIntegral X)
end ThreeAdicPlan
