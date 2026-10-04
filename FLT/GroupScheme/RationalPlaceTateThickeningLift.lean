/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceIntegralCoefficients
public import FLT.GroupScheme.PDivisibleIntegralTateCover

/-! # Simultaneous first-order lifts of the specified original Tate vectors -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The first-order reduction is an equivalence on all inverse-p sequences. -/
def rationalPlaceFirstOrderCoverEquiv (s : ℕ) :
    X.UniversalCover (ComplexIntegralThickening p 2 s) ≃
      X.UniversalCover (ComplexIntegerModPow p s) :=
  X.universalCoverSquareZeroEquiv (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_surjective p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide)) s (fun b _ ↦ by
      rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul])

/-- Lift every Tate coordinate simultaneously by the proved inverse-sequence equivalence. -/
def rationalPlaceTateThickeningLift (s : ℕ) (x : X.tateSequences) :
    X.UniversalCover (ComplexIntegralThickening p 2 s) :=
  (rationalPlaceFirstOrderCoverEquiv X s).symm
    (X.integralTateCover (rationalPlaceIntegralModPow p s) x)

/-- At first order, the n-th lifted coordinate already lives at original level n+s. -/
theorem rationalPlaceTateThickeningLift_finite (s n : ℕ) (x : X.tateSequences) :
    (rationalPlaceTateThickeningLift X s x).val n =
      X.pointColimitMk (n + s)
        (X.squareZeroLevelLift (rationalPlaceThickeningTheta p 2 s (by decide))
          (complexThickeningTheta_surjective p 2 s (by decide))
          (complexThickeningTheta_ker_pow p 2 s (by decide)) (p ^ s)
          (fun b _ ↦ by
            rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul])
          (n + s) ((rationalPlaceIntegralModPow p s).comp
            ((X.level (n + s)).integralPointCoordinate (X.tateEval (n + s) x)))) := rfl

/-- The lift reduces to the specified original Tate vector with its actual integral values. -/
theorem rationalPlaceTateThickeningLift_reduction (s : ℕ) (x : X.tateSequences) :
    X.universalCoverMap (rationalPlaceThickeningTheta p 2 s (by decide))
      (rationalPlaceTateThickeningLift X s x) =
        X.integralTateCover (rationalPlaceIntegralModPow p s) x :=
  (rationalPlaceFirstOrderCoverEquiv X s).apply_symm_apply _

/-- Any simultaneous lift of the same original Tate vector is this one. -/
theorem rationalPlaceTateThickeningLift_unique (s : ℕ) (x : X.tateSequences)
    (y : X.UniversalCover (ComplexIntegralThickening p 2 s))
    (hy : X.universalCoverMap (rationalPlaceThickeningTheta p 2 s (by decide)) y =
      X.integralTateCover (rationalPlaceIntegralModPow p s) x) :
    y = rationalPlaceTateThickeningLift X s x :=
  (rationalPlaceFirstOrderCoverEquiv X s).injective
    (hy.trans (rationalPlaceTateThickeningLift_reduction X s x).symm)

/-- Uniqueness proves compatibility across every p-power precision reduction. -/
theorem rationalPlaceTateThickeningLift_precision {s t : ℕ} (h : s ≤ t)
    (x : X.tateSequences) :
    X.universalCoverMap (rationalPlaceThickeningReduce p (le_refl 2) h)
      (rationalPlaceTateThickeningLift X t x) = rationalPlaceTateThickeningLift X s x := by
  apply rationalPlaceTateThickeningLift_unique
  rw [← X.universalCoverMap_comp, rationalPlaceThickeningTheta_reduce,
    X.universalCoverMap_comp, rationalPlaceTateThickeningLift_reduction]
  rfl

/-- Original Tate reductions commute with the lift at every coefficient precision. -/
theorem rationalPlaceTateThickeningLift_transition (s n : ℕ) (x : X.tateSequences) :
    X.pointColimitMul p ((rationalPlaceTateThickeningLift X s x).val (n + 1)) =
      (rationalPlaceTateThickeningLift X s x).val n :=
  (rationalPlaceTateThickeningLift X s x).property n

end ThreeAdicPlan
