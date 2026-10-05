/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceCartierDlogGalois
public import FLT.GroupScheme.RationalPlaceHodgeTateDlog

/-! # Galois equivariance of the actual integral and C_p Tate differentials -/

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

/-- Actual integral cotangent tensors are determined by their finite-level evaluations. -/
theorem rationalPlaceIntegralCotangentTensor_ext {v w : X.cotangentLimit ⊗[O] 𝓞_ℂ_[p]}
    (h : ∀ n, (X.cotangentEval n).rTensor 𝓞_ℂ_[p] v =
      (X.cotangentEval n).rTensor 𝓞_ℂ_[p] w) : v = w := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := rationalPlace_levelCotangent_finite X n
  have he : AdicCompletion.of (Ideal.span {(p : O)}) _ v =
      AdicCompletion.of (Ideal.span {(p : O)}) _ w := by
    apply X.completedCotangentTensor_ext
    exact h
  have hi := congrArg (rationalPlaceCompletedCotangentEquiv X) he
  simpa only [rationalPlaceCompletedCotangentEquiv_of] using hi

variable (σ : Field.absoluteGaloisGroup ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- Completion preserves equivariance of the original finite differentials. -/
theorem rationalPlaceHodgeTateDlogIntegral_galois (y : X.CartierTate) :
    (rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
      (rationalPlaceHodgeTateDlogIntegral X y) =
    rationalPlaceHodgeTateDlogIntegral X (σ • y) := by
  apply rationalPlaceIntegralCotangentTensor_ext X
  intro n
  have hn (v : X.cotangentLimit ⊗[O] 𝓞_ℂ_[p]) :
      (X.cotangentEval n).rTensor _
          ((rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _ v) =
        (rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
          ((X.cotangentEval n).rTensor _ v) := by
    induction v using TensorProduct.inductionOn with
    | tmul x c => rfl
    | add v w hv hw => simp only [map_add, hv, hw]
  rw [hn, rationalPlaceHodgeTateDlogIntegral_eval, rationalPlaceHodgeTateDlogIntegral_eval,
    rationalPlaceCartierDlogAt_galois]

/-- Inverting p preserves the actual original Galois action on the differential. -/
theorem rationalPlaceHodgeTateDlog_galois (y : X.CartierTate) :
    (rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
      (rationalPlaceHodgeTateDlog X y) = rationalPlaceHodgeTateDlog X (σ • y) := by
  have hn (v : X.cotangentLimit ⊗[O] 𝓞_ℂ_[p]) :
      (rationalPlaceComplexGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor _
          ((IsScalarTower.toAlgHom O 𝓞_ℂ_[p] ℂ_[p]).toLinearMap.lTensor _ v) =
        (IsScalarTower.toAlgHom O 𝓞_ℂ_[p] ℂ_[p]).toLinearMap.lTensor _
          ((rationalPlaceIntegerGalois (rationalPlaceGaloisEquiv p σ)).toLinearMap.lTensor
            _ v) := by
    induction v using TensorProduct.inductionOn with
    | tmul x c => rfl
    | add v w hv hw => simp only [map_add, hv, hw]
  unfold rationalPlaceHodgeTateDlog
  change _ = (IsScalarTower.toAlgHom O 𝓞_ℂ_[p] ℂ_[p]).toLinearMap.lTensor _
    (rationalPlaceHodgeTateDlogIntegral X (σ • y))
  simp only [LinearMap.comp_apply]
  rw [hn, rationalPlaceHodgeTateDlogIntegral_galois]
end ThreeAdicPlan
