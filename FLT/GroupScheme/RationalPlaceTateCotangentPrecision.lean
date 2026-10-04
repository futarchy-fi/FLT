/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateInfinitesimal
public import FLT.GroupScheme.PDivisibleInfinitesimalNaturality

/-! # Precision compatibility of the actual Tate cotangent functionals -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The original infinitesimal Tate points reduce compatibly at all p-power precisions. -/
theorem rationalPlaceTateInfinitesimal_precision {s t : ℕ} (h : s ≤ t) (x : X.tateSequences) :
    X.infinitesimalColimitMap (rationalPlaceThickeningTheta p 2 t (by decide))
      (rationalPlaceThickeningTheta p 2 s (by decide))
      (rationalPlaceThickeningReduce p (le_refl 2) h) (rationalPlaceIntegerModPowReduce p h)
      (rationalPlaceThickeningTheta_reduce p (le_refl 2) h (by decide))
      (rationalPlaceTateInfinitesimal X t x) = rationalPlaceTateInfinitesimal X s x := by
  apply Subtype.ext
  exact congrArg (fun z : X.UniversalCover (ComplexIntegralThickening p 2 s) ↦ z.val 0)
    (rationalPlaceTateThickeningLift_precision X h x)

/-- These cotangent functionals form a compatible integral system in the actual theta kernels. -/
theorem rationalPlaceTateCotangentFunctional_precision {s t : ℕ} (h : s ≤ t)
    (x : X.tateSequences) :
    (AlgHom.reductionKernelMap (rationalPlaceThickeningTheta p 2 t (by decide))
      (rationalPlaceThickeningTheta p 2 s (by decide))
      (rationalPlaceThickeningReduce p (le_refl 2) h) (rationalPlaceIntegerModPowReduce p h)
      (rationalPlaceThickeningTheta_reduce p (le_refl 2) h (by decide))).comp
        (rationalPlaceTateCotangentFunctional X t x) =
          rationalPlaceTateCotangentFunctional X s x := by
  let (i : ℕ) : Finite (X.LevelCotangent i) := rationalPlace_levelCotangent_finite X i
  have hn := X.nilpotentInfinitesimalCotangentEquiv_natural
    (rationalPlaceThickeningTheta p 2 t (by decide))
    (rationalPlaceThickeningTheta p 2 s (by decide))
    (rationalPlaceThickeningReduce p (le_refl 2) h) (rationalPlaceIntegerModPowReduce p h)
    (rationalPlaceThickeningTheta_reduce p (le_refl 2) h (by decide))
    (complexThickeningTheta_ker_pow p 2 t (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide))
    ⟨t, complexIntegralThickening_prime_pow p 2 t⟩
    ⟨s, complexIntegralThickening_prime_pow p 2 s⟩ (rationalPlaceTateInfinitesimal X t x)
  exact hn.symm.trans (congrArg (X.nilpotentInfinitesimalCotangentEquiv
    (rationalPlaceThickeningTheta p 2 s (by decide))
    (complexThickeningTheta_ker_pow p 2 s (by decide))
    ⟨s, complexIntegralThickening_prime_pow p 2 s⟩)
    (rationalPlaceTateInfinitesimal_precision X h x))

end ThreeAdicPlan
