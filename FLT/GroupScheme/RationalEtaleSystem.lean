/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalEtaleKernel

/-! # The étale quotient p-divisible system over the original rational-place base -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual étale quotient levels form a p-divisible system of their proved common height. -/
def rationalEtaleSystem :
    PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p X.rationalEtaleHeight where
  level := X.rationalEtaleLevel
  inclusion := X.rationalEtaleInclusion
  reduction := X.rationalEtaleReduction
  inclusion_refl := X.rationalEtaleInclusion_refl
  reduction_refl := X.rationalEtaleReduction_refl
  inclusion_comp := X.rationalEtaleInclusion_comp
  reduction_comp := X.rationalEtaleReduction_comp
  closed := X.rationalEtaleInclusion_closed
  faithfullyFlat := X.rationalEtaleReduction_faithfullyFlat
  kernel := X.rationalEtale_kernel
  inclusion_reduction := X.rationalEtaleInclusion_reduction
  reduction_inclusion := X.rationalEtaleReduction_inclusion
  killed := X.rationalEtaleLevel_killed
  rank := X.rationalEtale_rank
end ThreeAdicPlan.PDivisibleSystem
