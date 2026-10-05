/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalConnectedCotangentLevels
public import FLT.GroupScheme.PDivisibleVariableHeightCotangent
public import FLT.GroupScheme.RationalConnectedEtaleSystemExtension
public import FLT.GroupScheme.PDivisibleIntegralTangent

/-! # The original connected system retains the integral Lie module -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.PDivisibleSystem
variable {p height : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)

/-- Restriction to the original connected levels identifies their cotangent inverse limits. -/
def rationalConnectedCotangentEquiv :
    X.cotangentLimit ≃ₗ[O] X.rationalConnectedSystem.cotangentLimit :=
  LinearEquiv.ofBijective X.rationalConnectedSystemInclusion.cotangentMap
    (X.rationalConnectedSystemInclusion.cotangentMap_bijective
      (fun n ↦ (X.level n).rationalIdentityComponentInclusion_cotangent_bijective))

/-- The connected Lie identification is the dual of the actual cotangent restriction. -/
def rationalConnectedLieEquiv :
    X.rationalConnectedSystem.IntegralTangent ≃ₗ[O] X.IntegralTangent :=
  X.rationalConnectedCotangentEquiv.dualMap

/-- The Lie identification preserves evaluation on the original cotangent representatives. -/
theorem rationalConnectedLieEquiv_apply (d : X.rationalConnectedSystem.IntegralTangent)
    (v : X.cotangentLimit) :
    X.rationalConnectedLieEquiv d v = d (X.rationalConnectedCotangentEquiv v) := rfl

/-- The cotangent inverse limit of the actual étale quotient system is zero. -/
instance rationalEtaleCotangentLimitSubsingleton :
    Subsingleton X.rationalEtaleSystem.cotangentLimit := by
  constructor
  intro x y
  apply X.rationalEtaleSystem.cotangentLimit_ext
  intro n
  exact @Subsingleton.elim (X.level n).rationalComponentQuotient.Cotangent
    ((X.level n).rationalComponentQuotientCotangentSubsingleton) _ _

/-- The original étale quotient has zero integral Lie module. -/
instance rationalEtaleLieSubsingleton : Subsingleton X.rationalEtaleSystem.IntegralTangent := by
  infer_instance
end ThreeAdicPlan.PDivisibleSystem
