/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalConnectedSystem
public import FLT.GroupScheme.PDivisibleVariableHeightHom

/-! # The original connected inclusion on systems and Tate modules -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- The connected inclusion is a genuine morphism even when its height is smaller. -/
def rationalConnectedSystemInclusion : VariableHeightHom X.rationalConnectedSystem X where
  app := X.rationalConnectedEmbedding
  inclusion_naturality := X.rationalConnectedInclusion_naturality
  reduction_naturality := X.rationalConnectedReduction_naturality

/-- The original connected Tate-module inclusion is linear over the p-adic integers. -/
def rationalConnectedTateInclusion :
    X.rationalConnectedSystem.tateSequences →ₗ[ℤ_[p]] X.tateSequences :=
  X.rationalConnectedSystemInclusion.tateMap

/-- The original connected Tate-module inclusion is injective. -/
theorem rationalConnectedTateInclusion_injective :
    Function.Injective X.rationalConnectedTateInclusion := by
  intro x y h
  apply X.rationalConnectedSystem.tate_ext
  intro n
  apply (X.level n).rationalIdentityComponentInclusion_genericHom_injective
  exact congrArg (fun z ↦ X.tateEval n z) h
end ThreeAdicPlan.PDivisibleSystem
