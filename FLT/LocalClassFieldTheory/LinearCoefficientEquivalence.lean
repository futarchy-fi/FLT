/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuClassSubmodule

/-!
# Constructed linear equivalences on continuous coefficient classes

The inverse applies the inverse coefficient map to actual representatives.
No comparison isomorphism is supplied as a premise.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G F M N : Type*} [Group G] [TopologicalSpace G] [Field F]
  [AddCommGroup M] [Module F M] [DistribMulAction G M] [SMulCommClass G F M]
  [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup N] [Module F N] [DistribMulAction G N] [SMulCommClass G F N]
  [TopologicalSpace N] [DiscreteTopology N]
  (e : M ≃ₗ[F] N) (he : ∀ (g : G) (x : M), e (g • x) = g • e x)

omit [TopologicalSpace G] [SMulCommClass G F M] [TopologicalSpace M]
  [DiscreteTopology M] [SMulCommClass G F N] [TopologicalSpace N] [DiscreteTopology N] in
include he in
/-- Equivariance of the inverse coefficient map. -/
theorem linearCoefficientInverse_equivariant (g : G) (x : N) :
    e.symm (g • x) = g • e.symm x := by
  apply e.injective
  simp only [e.apply_symm_apply, he]

/-- The class equivalence constructed by applying the coefficient maps and their inverse. -/
def linearCoefficientClassEquiv :
    LinearContinuousClass F G M ≃ₗ[F] LinearContinuousClass F G N :=
  { linearCoefficientClass e.toLinearMap he with
    invFun := linearCoefficientClass e.symm.toLinearMap
      (linearCoefficientInverse_equivariant e he)
    left_inv := fun x => by
      induction x using Quotient.inductionOn with | h c =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        congr 1
        apply Subtype.ext
        apply ContinuousMap.ext
        intro g
        exact e.symm_apply_apply (c.1 g)
    right_inv := fun x => by
      induction x using Quotient.inductionOn with | h c =>
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        congr 1
        apply Subtype.ext
        apply ContinuousMap.ext
        intro g
        exact e.apply_symm_apply (c.1 g) }

variable [TopologicalSpace F] [DiscreteTopology F]

/-- The constructed class equivalence preserves and reflects the independent annihilator. -/
theorem linearCoefficientClassEquiv_peu (I : Subgroup G) (x : LinearContinuousClass F G M) :
    linearCoefficientClassEquiv e he x ∈ peuClassSubmodule I ↔ x ∈ peuClassSubmodule I :=
  peuClass_linearEquiv_iff I e he x

end LocalClassFieldTheory
