/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateInfinitesimalFinite
public import FLT.GroupScheme.SquareZeroPointLiftMultiplication
public import FLT.GroupScheme.InfinitesimalCotangentAddition

/-! # Additivity of the constructed original Tate tangent -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Addition of original Tate vectors becomes convolution of their actual finite lifts. -/
theorem rationalPlaceTateInfinitesimalAt_add (s : ℕ) (x z : X.tateSequences) :
    rationalPlaceTateInfinitesimalAt X s (x + z) =
      HopfAlgebra.augmentationKernelConv (rationalPlaceThickeningTheta p 2 s (by decide))
        (rationalPlaceTateInfinitesimalAt X s x) (rationalPlaceTateInfinitesimalAt X s z) := by
  apply Subtype.ext
  change X.squareZeroLevelLift (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_surjective p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide)) (p ^ s)
    (fun b _ ↦ by
      rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]) s
    ((rationalPlaceIntegralModPow p s).comp
      ((X.level s).integralPointCoordinate (X.tateEval s (x + z)))) = _
  rw [map_add, FF.integralPointCoordinate_add, integralPointCoefficient_mul]
  let : Module.Free ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (X.level s).CoordinateRing := Module.free_of_flat_of_isLocalRing
  exact HopfAlgebra.squareZeroPointLift_convMul
    (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_surjective p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide)) (p ^ s)
    (fun b _ ↦ by
      rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul]) _ _

/-- The actual original cotangent functional is additive in its Tate input. -/
theorem rationalPlaceTateCotangentFunctional_add (s : ℕ) (x z : X.tateSequences) :
    rationalPlaceTateCotangentFunctional X s (x + z) =
      rationalPlaceTateCotangentFunctional X s x + rationalPlaceTateCotangentFunctional X s z := by
  rw [rationalPlaceTateCotangentFunctional_at, rationalPlaceTateCotangentFunctional_at,
    rationalPlaceTateCotangentFunctional_at, rationalPlaceTateInfinitesimalAt_add]
  unfold PDivisibleSystem.infinitesimalLimitPairing
  rw [HopfAlgebra.augmentationPointCotangentEquiv_conv, LinearMap.add_comp]

/-- The actual integral tangent tensor is additive in its original Tate input. -/
theorem rationalPlaceTateTangentTensor_add (s : ℕ) (x z : X.tateSequences) :
    rationalPlaceTateTangentTensor X s (x + z) =
      rationalPlaceTateTangentTensor X s x + rationalPlaceTateTangentTensor X s z := by
  let e := X.integralTangentCoefficientsEquiv (M := RingHom.ker
    (rationalPlaceThickeningTheta p 2 s (by decide))) (rationalPlaceIntegersEquiv p).toRingEquiv
  apply e.injective
  exact (rationalPlaceTateTangentTensor_pairing X s (x + z)).trans
    ((rationalPlaceTateCotangentFunctional_add X s x z).trans
      ((congrArg₂ (· + ·) (rationalPlaceTateTangentTensor_pairing X s x).symm
        (rationalPlaceTateTangentTensor_pairing X s z).symm).trans (e.map_add _ _).symm))

/-- The constructed cotangent functional as an additive map on the original Tate module. -/
def rationalPlaceTateCotangentAddHom (s : ℕ) :
    X.tateSequences →+
      (X.cotangentLimit →ₗ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide))) :=
  AddMonoidHom.mk' (rationalPlaceTateCotangentFunctional X s)
    (rationalPlaceTateCotangentFunctional_add X s)

end ThreeAdicPlan
