/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Nonempty invariant cores of finite open orbits

The acting group can be infinite. Finiteness is required only of the orbit
of the open condition, as happens when its coefficients descend to a finite
extension. The constructed open controls every group element simultaneously.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteOrbitOpenCore
open Set
variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

/-- Points whose entire orbit lies in the prescribed open condition. -/
def core (U : Set X) : Set X := {x | ∀ g : G, g • x ∈ U}

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- The core is the intersection of the distinct translates, with repetitions removed. -/
theorem core_eq_sInter (U : Set X) :
    core (G := G) U = ⋂₀ Set.range (fun g : G ↦ (g • ·) ⁻¹' U) := by
  ext x
  simp only [core, mem_ofPred_eq, mem_sInter, mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, mem_preimage]

/-- A finite orbit of an open condition produces an open core even for an infinite group. -/
theorem isOpen_core {U : Set X} (hU : IsOpen U)
    (hf : (Set.range (fun g : G ↦ (g • ·) ⁻¹' U)).Finite) :
    IsOpen (core (G := G) U) := by
  rw [core_eq_sInter]
  apply hf.isOpen_sInter
  rintro _ ⟨g, rfl⟩
  exact hU.preimage (continuous_const_smul g)

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- Every core point satisfies the original condition. -/
theorem core_subset (U : Set X) : core (G := G) U ⊆ U := by
  intro x hx
  simpa only [one_smul] using hx 1

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- The core is preserved by every group element, not just a chosen finite list. -/
theorem smul_mem_core_iff (U : Set X) (g : G) (x : X) :
    g • x ∈ core (G := G) U ↔ x ∈ core (G := G) U := by
  constructor
  · intro h a
    simpa only [smul_smul, inv_mul_cancel_right] using h (a * g⁻¹)
  · intro h a
    simpa only [smul_smul] using h (a * g)

/-- Irreducibility keeps the finite invariant core nonempty. -/
theorem core_nonempty [IrreducibleSpace X] {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) (hf : (Set.range (fun g : G ↦ (g • ·) ⁻¹' U)).Finite) :
    (core (G := G) U).Nonempty := by
  classical
  have ho (V : Set X) (hV : V ∈ hf.toFinset) : IsOpen V := by
    obtain ⟨g, rfl⟩ := hf.mem_toFinset.mp hV
    exact hU.preimage (continuous_const_smul g)
  have hn (V : Set X) (hV : V ∈ hf.toFinset) : (Set.univ ∩ V).Nonempty := by
    obtain ⟨g, rfl⟩ := hf.mem_toFinset.mp hV
    obtain ⟨x, hx⟩ := hne
    exact ⟨g⁻¹ • x, trivial, by simpa using hx⟩
  have h := isIrreducible_iff_sInter.mp (IrreducibleSpace.isIrreducible_univ (X := X))
    hf.toFinset ho hn
  simpa only [Set.Finite.coe_toFinset, Set.univ_inter, ← core_eq_sInter] using h

end FLT.Mazur.FiniteOrbitOpenCore
