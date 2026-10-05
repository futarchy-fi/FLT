/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CotangentIdempotentKernel
public import FLT.GroupScheme.RationalComponentQuotientEtale

/-! # Original connected cotangents and vanishing étale cotangents -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
variable (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- The actual identity-component ideal is idempotent. -/
theorem rationalIdentityComponentIdeal_idempotent :
    IsIdempotentElem X.rationalIdentityComponentIdeal := by
  change Ideal.span {1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex} *
    Ideal.span {1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex} = _
  rw [Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun a ↦ Ideal.span {a})
    (componentIdempotent_isIdempotent (rationalSpecialIdeal p X.CoordinateRing)
      X.rationalIdentityComponentIndex).one_sub.eq

/-- The original connected embedding induces a bijection on actual integral cotangents. -/
theorem rationalIdentityComponentInclusion_cotangent_bijective :
    Function.Bijective X.rationalIdentityComponentInclusion.cotangentMap := by
  apply ModelHom.cotangentMap_bijective_of_idempotent_ker _
    X.rationalIdentityComponentInclusion_surjective
  rw [X.rationalIdentityComponentInclusion_ker]
  exact X.rationalIdentityComponentIdeal_idempotent

/-- The actual étale quotient has zero cotangent module at its identity. -/
instance rationalComponentQuotientCotangentSubsingleton :
    Subsingleton X.rationalComponentQuotient.Cotangent :=
  (Ideal.cotangent_subsingleton_iff _).mpr X.rationalComponentQuotient_augmentation_idempotent
end ThreeAdicPlan.FF
