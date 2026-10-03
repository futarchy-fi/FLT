/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousCupComparison
public import FLT.GaloisRepresentation.Extensions.PeuRamifiedClass

/-!
# The ordinary cup-annihilator in continuous cohomology

The independent explicit predicate is equivalent to vanishing of the actual
continuous-cohomology cup against inertia-trivial characters. Identifying
this cup with local Tate evaluation is a separate arithmetic theorem.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

variable {k G M : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- The annihilator of inertia-trivial characters under the actual continuous cup. -/
def IsPeuRamifiedCohomology (I : Subgroup G)
    (x : continuousCohomology 1 (TopRep.of (coefficientRepresentation k G M))) : Prop :=
  ∀ d : ContinuousAddCharacter G k, IsUnramifiedAddCharacter I d →
    continuousCohomologyCup x d = 0

/-- The cocycle predicate uses the existing continuous-cohomology cup. -/
theorem isPeuRamifiedCocycle_cohomology_iff (I : Subgroup G) (c : ContinuousCocycle G M) :
    IsPeuRamifiedCocycle (k := k) I c ↔
      IsPeuRamifiedCohomology (k := k) I (continuousH1Class (k := k) c) := by
  simp only [IsPeuRamifiedCocycle, IsPeuRamifiedCohomology, continuousCohomologyCup_eq_zero]

/-- The original splitting-class predicate is the continuous-cohomology cup-annihilator. -/
theorem isPeuRamifiedClass_cohomology_iff (I : Subgroup G) (x : ContinuousClass G M) :
    IsPeuRamifiedClass (k := k) I x ↔
      IsPeuRamifiedCohomology I (continuousH1Equiv (k := k) x) := by
  induction x using Quotient.inductionOn with | h c =>
    change IsPeuRamifiedCocycle (k := k) I c ↔
      IsPeuRamifiedCohomology I (continuousH1Equiv (k := k) (continuousClassMk c))
    rw [continuousH1Equiv_mk, isPeuRamifiedCocycle_cohomology_iff]

end GaloisRepresentation.Extensions
