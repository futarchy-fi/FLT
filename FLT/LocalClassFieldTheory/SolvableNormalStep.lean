/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A proper normal step for solvable noncyclic groups

Use the commutator subgroup when it is nontrivial, and a nontrivial cyclic
subgroup otherwise. This supplies the normal subgroup for degree induction.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

/-- A solvable group which is not cyclic has a nontrivial proper normal subgroup. -/
theorem solvable_noncyclic_normal_step (G : Type) [Group G] [Group.IsSolvable G]
    (hc : ¬ IsCyclic G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  have : Nontrivial G := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    exact hc inferInstance
  by_cases h : commutator G = ⊥
  · let : IsMulCommutative G := (commutator_eq_bot_iff G).mp h
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    refine ⟨Subgroup.zpowers g, inferInstance, ?_, ?_⟩
    · intro he
      have hm := Subgroup.mem_zpowers g
      rw [he, Subgroup.mem_bot] at hm
      exact hg hm
    · intro he
      exact hc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, he⟩)
  · exact ⟨commutator G, inferInstance, h,
      (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne⟩

end LocalClassFieldTheory
