/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudSimpleRepresentationQuotient
public import FLT.Mathlib.Topology.Algebra.ContinuousSMulDiscrete

/-!
# Discrete continuity of representation subquotients

Open evaluation fibres pass to invariant subspaces and quotients. For a
finite point space this is equivalent to continuity of the automorphism map
into its discrete target, the form used by the wild-inertia theorem.
-/

@[expose] public section
namespace Representation

variable {k G V : Type*} [Field k] [Group G] [TopologicalSpace G]
  [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- Evaluation fibres of a representation are open for a discrete continuous action. -/
def IsDiscreteContinuous : Prop := ∀ x y : V, IsOpen {g : G | ρ g x = y}

/-- On finite point spaces, open evaluation fibres give exactly automorphism-map continuity. -/
theorem continuous_toHomUnits_iff_discrete [Finite V]
    [TopologicalSpace (Module.End k V)ˣ] [DiscreteTopology (Module.End k V)ˣ] :
    Continuous ρ.toHomUnits ↔ ρ.IsDiscreteContinuous := by
  constructor
  · intro h x y
    exact h.isOpen_preimage {a | (a : Module.End k V) x = y} (isOpen_discrete _)
  · intro h
    apply continuous_discrete_rng.mpr
    intro a
    have he : ρ.toHomUnits ⁻¹' {a} = ⋂ x : V, {g : G | ρ g x = (a : Module.End k V) x} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      exact Units.ext_iff.trans LinearMap.ext_iff
    rw [he]
    exact isOpen_iInter_of_finite fun x ↦ h x _

/-- A stable subspace inherits discrete continuity. -/
theorem IsDiscreteContinuous.subrepresentation (hρ : ρ.IsDiscreteContinuous)
    (W : Subrepresentation ρ) : W.toRepresentation.IsDiscreteContinuous := by
  intro x y
  have he : {g : G | W.toRepresentation g x = y} = {g : G | ρ g x.val = y.val} := by
    ext g
    exact Subtype.ext_iff
  rw [he]
  exact hρ x.val y.val

/-- The quotient by a stable subspace inherits discrete continuity. -/
theorem IsDiscreteContinuous.quotient (hρ : ρ.IsDiscreteContinuous)
    (W : Subrepresentation ρ) :
    (ρ.quotient W.toSubmodule W.apply_mem_toSubmodule).IsDiscreteContinuous := by
  intro x y
  obtain ⟨v, rfl⟩ := W.toSubmodule.mkQ_surjective x
  have he : {g : G | (ρ.quotient W.toSubmodule W.apply_mem_toSubmodule) g
      (W.toSubmodule.mkQ v) = y} =
      ⋃ w : {w : V // W.toSubmodule.mkQ w = y}, {g : G | ρ g v = w.val} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hg
      exact ⟨⟨ρ g v, hg⟩, rfl⟩
    · rintro ⟨w, hw⟩
      change W.toSubmodule.mkQ (ρ g v) = y
      rw [hw]
      exact w.property
  rw [he]
  exact isOpen_iUnion fun w ↦ hρ v w.val

end Representation
