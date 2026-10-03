/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousCup

/-!
# An independent ordinary peu-ramification predicate

The predicate is the continuous cup-annihilator of trivial characters
vanishing on inertia, following GHLS, Definition 2.1.2, in the ordinary
cyclotomic case. It mentions neither Kummer units nor finite-flat models.
Its comparison with the local Tate pairing and the unit criterion remains
an arithmetic theorem to prove, not a premise built into this definition.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G k M : Type*} [Group G] [TopologicalSpace G]
    [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] (I : Subgroup G)

/-- A trivial-coefficient character is unramified when it vanishes on inertia. -/
def IsUnramifiedAddCharacter (d : ContinuousAddCharacter G k) : Prop :=
  ∀ g ∈ I, d.1 g = 0

/-- The independent continuous cup-annihilator condition on an ordinary cocycle. -/
def IsPeuRamifiedCocycle (c : ContinuousCocycle G M) : Prop :=
  ∀ d : ContinuousAddCharacter G k, IsUnramifiedAddCharacter I d →
    ContinuousIsCoboundaryTwo (continuousCup c d)

/-- Changing the splitting preserves and reflects the independent condition. -/
theorem isPeuRamifiedCocycle_splitting_iff (c c' : ContinuousCocycle G M)
    (h : SplittingEquivalent (fun g ↦ c.1 g) (fun g ↦ c'.1 g)) :
    IsPeuRamifiedCocycle (k := k) I c' ↔ IsPeuRamifiedCocycle (k := k) I c := by
  constructor
  · intro hc d hd
    exact (continuousCup_splitting_iff c c' d h).mp (hc d hd)
  · intro hc d hd
    exact (continuousCup_splitting_iff c c' d h).mpr (hc d hd)

/-- The cup-annihilator condition descends to the existing continuous class quotient. -/
def IsPeuRamifiedClass (x : ContinuousClass G M) : Prop :=
  Quotient.lift (IsPeuRamifiedCocycle (k := k) I)
    (fun c c' h ↦ propext (isPeuRamifiedCocycle_splitting_iff I c c' h).symm) x

/-- The descended predicate is exactly the independent cocycle condition. -/
@[simp] theorem isPeuRamifiedClass_mk (c : ContinuousCocycle G M) :
    IsPeuRamifiedClass (k := k) I (continuousClassMk c) ↔ IsPeuRamifiedCocycle (k := k) I c :=
  Iff.rfl

/-- The split extension has vanishing cup against every unramified character. -/
theorem isPeuRamifiedClass_zero :
    IsPeuRamifiedClass (k := k) I
      (linearClassEquiv (0 : LinearContinuousClass k G M)) := by
  intro d _
  refine ⟨0, fun g h ↦ ?_⟩
  change g • (0 : M) - 0 + 0 = d.1 h • (0 : M)
  simp

/-- Every class represented by a principal continuous cocycle satisfies the condition. -/
theorem isPeuRamifiedClass_of_principal (c : ContinuousCocycle G M)
    (h : SplittingEquivalent (fun _ : G ↦ (0 : M)) (fun g ↦ c.1 g)) :
    IsPeuRamifiedClass (k := k) I (continuousClassMk c) := by
  have hc : continuousClassMk c = linearClassEquiv (0 : LinearContinuousClass k G M) :=
    (continuousClassMk_eq_iff _ _).mpr (splittingEquivalent_equivalence.symm h)
  rw [hc]
  exact isPeuRamifiedClass_zero I

end GaloisRepresentation.Extensions
