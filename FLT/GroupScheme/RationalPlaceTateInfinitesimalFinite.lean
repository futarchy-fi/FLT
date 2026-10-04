/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateInfinitesimal

/-! # The specified finite representative of the infinitesimal Tate lift -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The zeroth simultaneous lift has its specified representative at original level s. -/
theorem rationalPlaceTateInfinitesimal_finite (s : ℕ) (x : X.tateSequences) :
    (rationalPlaceTateInfinitesimal X s x).val =
      X.pointColimitMk s
        (X.squareZeroLevelLift (rationalPlaceThickeningTheta p 2 s (by decide))
          (complexThickeningTheta_surjective p 2 s (by decide))
          (complexThickeningTheta_ker_pow p 2 s (by decide)) (p ^ s)
          (fun b _ ↦ by
            rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul])
          s ((rationalPlaceIntegralModPow p s).comp
            ((X.level s).integralPointCoordinate (X.tateEval s x)))) := by
  change (rationalPlaceTateThickeningLift X s x).val 0 = _
  rw [rationalPlaceTateThickeningLift_finite, Nat.zero_add]

/-- This particular finite representative itself reduces to the original augmentation. -/
def rationalPlaceTateInfinitesimalAt (s : ℕ) (x : X.tateSequences) :
    X.LevelInfinitesimalKernel (rationalPlaceThickeningTheta p 2 s (by decide)) s := by
  let f := X.squareZeroLevelLift (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_surjective p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide)) (p ^ s)
    (fun b _ ↦ by
      rw [nsmul_eq_mul, Nat.cast_pow, complexIntegralThickening_prime_pow, zero_mul])
    s ((rationalPlaceIntegralModPow p s).comp
      ((X.level s).integralPointCoordinate (X.tateEval s x)))
  refine ⟨f, ?_⟩
  apply X.pointColimitMk_injective s
  change X.pointColimitMap _ (X.pointColimitMk s f) = _
  rw [← rationalPlaceTateInfinitesimal_finite X s x,
    (rationalPlaceTateInfinitesimal X s x).property]
  exact (X.pointColimitMk_augmentation s).symm

/-- The explicit representative retains the actual simultaneous lift, without a choice of level. -/
theorem rationalPlaceTateInfinitesimalAt_represents (s : ℕ) (x : X.tateSequences) :
    X.infinitesimalColimitMk _ s (rationalPlaceTateInfinitesimalAt X s x) =
      rationalPlaceTateInfinitesimal X s x :=
  Subtype.ext (rationalPlaceTateInfinitesimal_finite X s x).symm

/-- The original limit functional is computed on this exact finite representative. -/
theorem rationalPlaceTateCotangentFunctional_at (s : ℕ) (x : X.tateSequences) :
    rationalPlaceTateCotangentFunctional X s x =
      X.infinitesimalLimitPairing (rationalPlaceThickeningTheta p 2 s (by decide))
        (complexThickeningTheta_ker_pow p 2 s (by decide)) s
        (rationalPlaceTateInfinitesimalAt X s x) :=
  rationalPlaceTateCotangentFunctional_finite X s s x _
    (rationalPlaceTateInfinitesimalAt_represents X s x)

end ThreeAdicPlan
