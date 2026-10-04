/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuCoefficientTransport

/-!
# The independent annihilator as a class submodule

The submodule operations descend from actual cocycles. Equivariant linear
coefficient isomorphisms preserve and reflect its membership.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open GaloisRepresentation.Extensions

variable {G F M N : Type*} [Group G] [TopologicalSpace G]
  [Field F] [TopologicalSpace F] [DiscreteTopology F]
  [AddCommGroup M] [Module F M] [DistribMulAction G M] [SMulCommClass G F M]
  [TopologicalSpace M] [DiscreteTopology M]
  [AddCommGroup N] [Module F N] [DistribMulAction G N] [SMulCommClass G F N]
  [TopologicalSpace N] [DiscreteTopology N]

/-- The original independent predicate defines a subspace of continuous classes. -/
def peuClassSubmodule (I : Subgroup G) : Submodule F (LinearContinuousClass F G M) where
  carrier := {x | IsPeuRamifiedClass (k := F) I (linearClassEquiv x)}
  zero_mem' := isPeuRamifiedClass_zero I
  add_mem' := by
    intro x y
    induction x using Quotient.inductionOn with | h c =>
      induction y using Quotient.inductionOn with | h d =>
        exact (peuCocycleSubmodule I).add_mem
  smul_mem' := by
    intro a x
    induction x using Quotient.inductionOn with | h c =>
      exact (peuCocycleSubmodule I).smul_mem a

/-- Equivariant linear coefficient isomorphisms preserve and reflect the class predicate. -/
theorem peuClass_linearEquiv_iff (I : Subgroup G) (e : M ≃ₗ[F] N)
    (he : ∀ (g : G) (x : M), e (g • x) = g • e x)
    (x : LinearContinuousClass F G M) :
    linearCoefficientClass e.toLinearMap he x ∈ peuClassSubmodule I ↔
      x ∈ peuClassSubmodule I := by
  induction x using Quotient.inductionOn with | h c =>
    exact isPeuRamified_linearEquiv_iff I e he c

end LocalClassFieldTheory
