/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierReducedUnramified
public import FLT.GroupScheme.RationalPlaceTateReducedCartier

/-! # The actual reduced Tate pairing vanishes at unramified levels -/

@[expose] public noncomputable section
open PadicHodgeTheory HopfAlgebra.CartierDual
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

local instance unramifiedLevelFree (n : ℕ) : Module.Free
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) (X.level n).CoordinateRing :=
  Module.free_of_flat_of_isLocalRing

/-- At an unramified level the constructed reduced Cartier pairing is identically zero. -/
theorem rationalPlaceTateReducedCartier_unramified (s : ℕ)
    [Algebra.FormallyUnramified ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (X.level s).CoordinateRing] (y : X.CartierTate) (x : X.tateSequences) :
    rationalPlaceTateReducedCartier X s y x = 0 := by
  apply Subtype.ext
  change (rationalPlaceTateReducedCartier X s y x : ComplexIntegralThickening p 2 s) = 0
  rw [rationalPlaceTateReducedCartier_finite X s s y x _
    (rationalPlaceTateInfinitesimalAt_represents X s x)]
  exact reducedLogDifferential_unramified _ _ _ _ _

end ThreeAdicPlan
