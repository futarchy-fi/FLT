/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateThickeningLift
public import FLT.GroupScheme.PDivisibleTateInfinitesimal
public import FLT.GroupScheme.PDivisibleIntegralInfinitesimal

/-! # The actual lifted Tate vector gives an original integral tangent tensor -/

@[expose] public noncomputable section
open PadicHodgeTheory
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The zeroth lifted coordinate is an actual infinitesimal point, with no lift premise. -/
def rationalPlaceTateInfinitesimal (s : ℕ) (x : X.tateSequences) :
    X.InfinitesimalColimit (rationalPlaceThickeningTheta p 2 s (by decide)) :=
  X.liftedTateInfinitesimal _ (rationalPlaceIntegralModPow p s) x
    (rationalPlaceTateThickeningLift X s x) (rationalPlaceTateThickeningLift_reduction X s x)

/-- Its original cotangent functional takes values in the actual integral theta kernel. -/
def rationalPlaceTateCotangentFunctional (s : ℕ) (x : X.tateSequences) :
    X.cotangentLimit →ₗ[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide)) :=
  rationalPlaceFormalInfinitesimalCotangentEquiv X
    (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide))
    ⟨s, complexIntegralThickening_prime_pow p 2 s⟩ (rationalPlaceTateInfinitesimal X s x)

/-- The original integral tangent tensor representing this particular lifted Tate vector. -/
def rationalPlaceTateTangentTensor (s : ℕ) (x : X.tateSequences) :
    X.IntegralTangent ⊗[(LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
      RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide)) :=
  (X.integralTangentInfinitesimalEquiv (rationalPlaceIntegersEquiv p).toRingEquiv
      (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide))
    ⟨s, complexIntegralThickening_prime_pow p 2 s⟩).symm (rationalPlaceTateInfinitesimal X s x)

/-- The constructed tensor represents the actual zeroth lifted point. -/
theorem rationalPlaceTateTangentTensor_represents (s : ℕ) (x : X.tateSequences) :
    X.integralTangentInfinitesimalEquiv (rationalPlaceIntegersEquiv p).toRingEquiv
      (rationalPlaceThickeningTheta p 2 s (by decide))
      (complexThickeningTheta_ker_pow p 2 s (by decide))
      ⟨s, complexIntegralThickening_prime_pow p 2 s⟩ (rationalPlaceTateTangentTensor X s x) =
        rationalPlaceTateInfinitesimal X s x :=
  Equiv.apply_symm_apply _ _

/-- The tensor contracts to the same original cotangent functional. -/
theorem rationalPlaceTateTangentTensor_pairing (s : ℕ) (x : X.tateSequences) :
    X.integralTangentCoefficientsEquiv (rationalPlaceIntegersEquiv p).toRingEquiv
      (rationalPlaceTateTangentTensor X s x) = rationalPlaceTateCotangentFunctional X s x := by
  let (i : ℕ) : Finite (X.LevelCotangent i) := rationalPlace_levelCotangent_finite X i
  let e := X.nilpotentInfinitesimalCotangentEquiv
    (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide))
    ⟨s, complexIntegralThickening_prime_pow p 2 s⟩
  have he := congrArg e (rationalPlaceTateTangentTensor_represents X s x)
  change e (e.symm (X.integralTangentCoefficientsEquiv
    (rationalPlaceIntegersEquiv p).toRingEquiv (rationalPlaceTateTangentTensor X s x))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact he

/-- Any finite representative of the actual lifted point computes the same cotangent functional. -/
theorem rationalPlaceTateCotangentFunctional_finite (s n : ℕ) (x : X.tateSequences)
    (f : X.LevelInfinitesimalKernel (rationalPlaceThickeningTheta p 2 s (by decide)) n)
    (hf : X.infinitesimalColimitMk _ n f = rationalPlaceTateInfinitesimal X s x) :
    rationalPlaceTateCotangentFunctional X s x =
      X.infinitesimalLimitPairing (rationalPlaceThickeningTheta p 2 s (by decide))
        (complexThickeningTheta_ker_pow p 2 s (by decide)) n f := by
  let (i : ℕ) : Finite (X.LevelCotangent i) := rationalPlace_levelCotangent_finite X i
  change X.nilpotentInfinitesimalCotangentEquiv _ _ _ _ = _
  rw [← hf]
  exact X.nilpotentInfinitesimalCotangentEquiv_mk _ _ _ n f

end ThreeAdicPlan
