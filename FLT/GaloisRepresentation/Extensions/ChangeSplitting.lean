/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.CocycleAction
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Changing a splitting of an extension

Changing a lift by a coefficient vector adds a principal crossed
homomorphism. This gives an equivalence relation on cocycles without
assuming an identification with derived continuous cohomology.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- Change a cocycle representative by the coefficient vector `a`. -/
def changeSplitting (c : G → M) (a : M) (g : G) : M := c g + (g • a - a)

/-- Changing the splitting preserves the cocycle identity. -/
theorem changeSplitting_isCocycle {c : G → M} (hc : groupCohomology.IsCocycle₁ c)
    (a : M) : groupCohomology.IsCocycle₁ (changeSplitting c a) := by
  intro g h
  simp only [changeSplitting, hc g h, smul_add, smul_sub, mul_smul]
  abel

/-- The zero vector does not change a splitting. -/
@[simp] theorem changeSplitting_zero (c : G → M) : changeSplitting c 0 = c := by
  funext g
  simp [changeSplitting]

/-- Successive changes of splitting add their coefficient vectors. -/
theorem changeSplitting_add (c : G → M) (a b : M) :
    changeSplitting (changeSplitting c a) b = changeSplitting c (a + b) := by
  funext g
  simp only [changeSplitting, smul_add]
  abel

/-- Two representatives differ by a change of splitting. -/
def SplittingEquivalent (c d : G → M) : Prop := ∃ a : M, d = changeSplitting c a

/-- Changes of splitting define an equivalence relation, before restricting to cocycles. -/
theorem splittingEquivalent_equivalence : Equivalence (SplittingEquivalent (G := G) (M := M)) := by
  refine ⟨fun c ↦ ⟨0, (changeSplitting_zero c).symm⟩, ?_, ?_⟩
  · rintro c d ⟨a, rfl⟩
    exact ⟨-a, by rw [changeSplitting_add, add_neg_cancel, changeSplitting_zero]⟩
  · rintro c d e ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, changeSplitting_add c a b⟩

/-- This relation is exactly the usual coboundary condition on the difference. -/
theorem splittingEquivalent_iff_coboundary (c d : G → M) :
    SplittingEquivalent c d ↔ groupCohomology.IsCoboundary₁ (fun g ↦ d g - c g) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, fun g ↦ by simp [changeSplitting]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, funext fun g ↦ ?_⟩
    dsimp [changeSplitting]
    rw [ha g]
    simp only [← add_sub_assoc, add_sub_cancel_left]

variable [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- A continuous orbit map makes a change of splitting continuous. -/
theorem continuous_changeSplitting {c : G → M} (hc : Continuous c) (a : M)
    (ha : Continuous (fun g : G ↦ g • a)) : Continuous (changeSplitting c a) :=
  hc.add (ha.sub continuous_const)

end GaloisRepresentation.Extensions
