/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateInfinitesimalFinite
public import FLT.GroupScheme.PDivisibleReducedCartierPairing

/-! # Original Cartier differentials on the constructed infinitesimal Tate points -/

@[expose] public noncomputable section
open PadicHodgeTheory HopfAlgebra.CartierDual
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

local instance levelFree (n : ℕ) : Module.Free
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) (X.level n).CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- The differential of the original dual Tate character on the actual lifted Tate point. -/
def rationalPlaceTateReducedCartier (s : ℕ) (y : X.CartierTate) (x : X.tateSequences) :
    RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide)) :=
  X.reducedCartierPairing (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_surjective p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide)) (rationalPlaceIntegralModPow p s)
    s (fun b ↦ by
      apply Subtype.ext
      change p ^ s • (b : ComplexIntegralThickening p 2 s) = 0
      rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul])
    y (rationalPlaceTateInfinitesimal X s x)

/-- Any actual finite representative computes the same value. -/
theorem rationalPlaceTateReducedCartier_finite (s n : ℕ) (y : X.CartierTate)
    (x : X.tateSequences)
    (f : X.LevelInfinitesimalKernel (rationalPlaceThickeningTheta p 2 s (by decide)) n)
    (hf : X.infinitesimalColimitMk _ n f = rationalPlaceTateInfinitesimal X s x) :
    (rationalPlaceTateReducedCartier X s y x : ComplexIntegralThickening p 2 s) =
      X.reducedCartierAt (rationalPlaceThickeningTheta p 2 s (by decide))
        (complexThickeningTheta_surjective p 2 s (by decide))
        (complexThickeningTheta_ker_pow p 2 s (by decide)) (rationalPlaceIntegralModPow p s)
        n y f := by
  unfold rationalPlaceTateReducedCartier
  rw [← hf]
  exact X.reducedCartierPairing_mk _ _ _ _ _ _ _ _ _

/-- At the specified level s, the actual point evaluates by its original cotangent contraction. -/
theorem rationalPlaceTateReducedCartier_cotangent (s : ℕ) (y : X.CartierTate)
    (x : X.tateSequences) :
    (rationalPlaceTateReducedCartier X s y x : ComplexIntegralThickening p 2 s) =
      LinearMap.mul' ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) _
        (((RingHom.ker (rationalPlaceThickeningTheta p 2 s (by decide))).subtype.restrictScalars
          ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)).comp
          (AlgHom.augmentationPointCotangentEquiv _
            (rationalPlaceThickeningTheta p 2 s (by decide))
            (complexThickeningTheta_ker_pow p 2 s (by decide))
            (rationalPlaceTateInfinitesimalAt X s x)) |>.rTensor _ <|
              linearTestDlog (linearCharacterLift
                (rationalPlaceThickeningTheta p 2 s (by decide))
                (complexThickeningTheta_surjective p 2 s (by decide))
                ((rationalPlaceIntegralModPow p s).comp
                  (X.cartierTateIntegralCoordinate s y)))) := by
  rw [rationalPlaceTateReducedCartier_finite X s s y x _
    (rationalPlaceTateInfinitesimalAt_represents X s x)]
  exact reducedLogDifferential_point_cotangent _ _ _ _ _

end ThreeAdicPlan
