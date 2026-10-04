/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateReducedCartier

/-! # The reduced original Cartier value is contraction of the constructed tangent tensor -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory HopfAlgebra.CartierDual
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual theta kernel is annihilated by the specified p-power precision. -/
theorem rationalPlaceFirstOrderKernel_killed (s : ℕ)
    (b : RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide))) : p ^ s • b = 0 := by
  apply Subtype.ext
  change p ^ s • (b : ComplexIntegralThickening p 2 s) = 0
  rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]

/-- The finite differential is the level reduction of the actual integral tangent tensor. -/
theorem rationalPlaceTateTangentTensor_at (s : ℕ) (x : X.tateSequences) :
    X.integralTangentLevelCoefficientsEquiv (rationalPlaceIntegersEquiv p).toRingEquiv
      s (rationalPlaceFirstOrderKernel_killed s) (rationalPlaceTateTangentTensor X s x) =
        AlgHom.augmentationPointCotangentEquiv _
          (rationalPlaceThickeningTheta p 2 s (by decide))
          (complexThickeningTheta_ker_pow p 2 s (by decide))
          (rationalPlaceTateInfinitesimalAt X s x) := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := rationalPlace_levelCotangent_finite X n
  apply (X.cotangentTorsionEquiv s (rationalPlaceFirstOrderKernel_killed s)).injective
  change X.cotangentTorsionEquiv s (rationalPlaceFirstOrderKernel_killed s)
    ((X.cotangentTorsionEquiv s (rationalPlaceFirstOrderKernel_killed s)).symm
      (X.integralTangentCoefficientsEquiv (rationalPlaceIntegersEquiv p).toRingEquiv
        (rationalPlaceTateTangentTensor X s x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (rationalPlaceTateTangentTensor_pairing X s x).trans
    (rationalPlaceTateCotangentFunctional_at X s x)

/-- Any linear lift of the original dual character contracts against the actual Tate tangent. -/
theorem rationalPlaceTateReducedCartier_tensor (s : ℕ) (y : X.CartierTate)
    (x : X.tateSequences)
    (χ : HopfAlgebra.CartierDual
      ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (X.level s).CoordinateRing →ₗ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
        ComplexIntegralThickening p 2 s)
    (hχ : (rationalPlaceThickeningTheta p 2 s (by decide)).toLinearMap.comp χ =
      ((rationalPlaceIntegralModPow p s).comp (X.cartierTateIntegralCoordinate s y)).toLinearMap) :
    (rationalPlaceTateReducedCartier X s y x : ComplexIntegralThickening p 2 s) =
      LinearMap.mul' ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) _
        (((RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide))).subtype.restrictScalars
          ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)).comp
          (X.integralTangentLevelCoefficientsEquiv (rationalPlaceIntegersEquiv p).toRingEquiv
            s (rationalPlaceFirstOrderKernel_killed s) (rationalPlaceTateTangentTensor X s x))
          |>.rTensor _ <| linearTestDlog χ) := by
  let : Module.Free ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (X.level s).CoordinateRing := Module.free_of_flat_of_isLocalRing
  rw [rationalPlaceTateTangentTensor_at]
  exact (rationalPlaceTateReducedCartier_finite X s s y x _
    (rationalPlaceTateInfinitesimalAt_represents X s x)).trans
      (reducedLogDifferential_point_lift (rationalPlaceThickeningTheta p 2 s (by decide))
        (complexThickeningTheta_surjective p 2 s (by decide))
        (complexThickeningTheta_ker_pow p 2 s (by decide))
        ((rationalPlaceIntegralModPow p s).comp (X.cartierTateIntegralCoordinate s y))
        χ hχ (rationalPlaceTateInfinitesimalAt X s x))

end ThreeAdicPlan
