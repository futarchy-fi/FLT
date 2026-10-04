/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalConnectedRanks

/-! # The connected p-divisible system over the original rational-place base -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The actual connected levels form a p-divisible system of their proved common height. -/
def rationalConnectedSystem :
    PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p X.rationalConnectedHeight where
  level := X.rationalConnectedLevel
  inclusion := X.rationalConnectedInclusion
  reduction := X.rationalConnectedReduction
  inclusion_refl := X.rationalConnectedInclusion_refl
  reduction_refl := X.rationalConnectedReduction_refl
  inclusion_comp := X.rationalConnectedInclusion_comp
  reduction_comp := X.rationalConnectedReduction_comp
  closed := X.rationalConnectedInclusion_closed
  faithfullyFlat := X.rationalConnectedReduction_faithfullyFlat
  kernel := X.rationalConnected_kernel
  inclusion_reduction := X.rationalConnectedInclusion_reduction
  reduction_inclusion := X.rationalConnectedReduction_inclusion
  killed := X.rationalConnectedLevel_killed
  rank := X.rationalConnected_rank
end ThreeAdicPlan.PDivisibleSystem
