/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalPlaceTateThickeningLift
public import FLT.GroupScheme.PDivisibleNilpotentUniversalCover

/-! # Original Tate lifts compatible in theta, p-power and Tate precision -/

@[expose] public noncomputable section
open PadicHodgeTheory
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- All positive integral theta orders induce equivalences of original inverse-p sequences. -/
def rationalPlaceThickeningCoverEquiv (r s : ℕ) (hr : 0 < r) :
    X.UniversalCover (ComplexIntegralThickening p r s) ≃
      X.UniversalCover (ComplexIntegerModPow p s) :=
  Equiv.ofBijective (X.universalCoverMap (rationalPlaceThickeningTheta p r s hr))
    (X.universalCoverMap_bijective_nilpotent _
      (complexThickeningTheta_surjective p r s hr)
      ⟨r, complexThickeningTheta_ker_pow p r s hr⟩
      ⟨s, complexIntegralThickening_prime_pow p r s⟩)

/-- Lift the specified original Tate vector simultaneously at any integral coefficient precision. -/
def rationalPlaceTatePrecisionLift (r s : ℕ) (hr : 0 < r) (x : X.tateSequences) :
    X.UniversalCover (ComplexIntegralThickening p r s) :=
  (rationalPlaceThickeningCoverEquiv X r s hr).symm
    (X.integralTateCover (rationalPlaceIntegralModPow p s) x)

/-- Its theta reduction has precisely the original integral Tate coordinates. -/
theorem rationalPlaceTatePrecisionLift_reduction (r s : ℕ) (hr : 0 < r) (x : X.tateSequences) :
    X.universalCoverMap (rationalPlaceThickeningTheta p r s hr)
      (rationalPlaceTatePrecisionLift X r s hr x) =
        X.integralTateCover (rationalPlaceIntegralModPow p s) x :=
  (rationalPlaceThickeningCoverEquiv X r s hr).apply_symm_apply _

/-- The simultaneous lift is unique at every positive theta order. -/
theorem rationalPlaceTatePrecisionLift_unique (r s : ℕ) (hr : 0 < r) (x : X.tateSequences)
    (y : X.UniversalCover (ComplexIntegralThickening p r s))
    (hy : X.universalCoverMap (rationalPlaceThickeningTheta p r s hr) y =
      X.integralTateCover (rationalPlaceIntegralModPow p s) x) :
    y = rationalPlaceTatePrecisionLift X r s hr x :=
  (rationalPlaceThickeningCoverEquiv X r s hr).injective
    (hy.trans (rationalPlaceTatePrecisionLift_reduction X r s hr x).symm)

/-- All theta and p-power reductions commute with the unique Tate lift. -/
theorem rationalPlaceTatePrecisionLift_reduce {r r' s s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') (hr₀ : 0 < r) (x : X.tateSequences) :
    X.universalCoverMap (rationalPlaceThickeningReduce p hr hs)
      (rationalPlaceTatePrecisionLift X r' s' (hr₀.trans_le hr) x) =
        rationalPlaceTatePrecisionLift X r s hr₀ x := by
  apply rationalPlaceTatePrecisionLift_unique
  rw [← X.universalCoverMap_comp, rationalPlaceThickeningTheta_reduce,
    X.universalCoverMap_comp, rationalPlaceTatePrecisionLift_reduction]
  rfl

/-- At order two the general lift is the explicit shifted square-zero lift. -/
theorem rationalPlaceTatePrecisionLift_order_two (s : ℕ) (x : X.tateSequences) :
    rationalPlaceTatePrecisionLift X 2 s (by decide) x =
      rationalPlaceTateThickeningLift X s x :=
  rationalPlaceTateThickeningLift_unique X s x _
    (rationalPlaceTatePrecisionLift_reduction X 2 s (by decide) x)

end ThreeAdicPlan
