/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DirectLimitFiniteRelation
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Flatness of directed module colimits over a fixed base

Finite relations descend to a stage, where flatness supplies witnesses.
Mapping those witnesses back proves the equational criterion in the limit.
-/

@[expose] public noncomputable section
namespace Module.Flat
variable {R ι : Type*} [CommRing R] [Preorder ι] [DecidableEq ι]
  [Nonempty ι] [IsDirectedOrder ι] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (f · · ·)]

/-- Directed colimits of flat modules are flat; transition maps may have kernels. -/
theorem directLimit [∀ i, Flat R (G i)] : Flat R (DirectLimit G f) := by
  apply of_forall_isTrivialRelation
  intro l a x hx
  obtain ⟨i, y, hy, ha⟩ := DirectLimit.exists_of_finite_relation f a x hx
  obtain ⟨n, c, z, hz, hc⟩ := isTrivialRelation_of_sum_smul_eq_zero ha
  refine ⟨n, c, fun j ↦ DirectLimit.of R ι G f i (z j), ?_, hc⟩
  intro k
  rw [← hy k, hz k, map_sum]
  simp only [map_smul]

end Module.Flat
