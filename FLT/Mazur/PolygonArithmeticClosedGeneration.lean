/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticDegreeFinite
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType

/-!
# Lifting homogeneous generation from the original closed stage

The proved finite homogeneous modules allow Nakayama to lift generation
degree by degree. A subalgebra containing homogeneous lifts of every closed
stage section consequently contains the entire compatible Veronese algebra.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n] [IsAdicComplete (ideal A π) A]

/-- Generating the actual closed-stage image suffices to generate the whole compatible degree. -/
theorem exactVeroneseDegree_submodule_eq_top (d : ℕ)
    (P : Submodule (A)
      (compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d))
    (hP : ∀ s, ∃ t ∈ P,
      compatibleDegreeEval A π n h 0 (exactVeroneseStep A π hne hgen n h * d) t =
        compatibleDegreeEval A π n h 0 (exactVeroneseStep A π hne hgen n h * d) s) : P = ⊤ := by
  let _ := exactVeroneseDegree_finite A π hne hgen n h d
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsAdicComplete.le_jacobson_bot (ideal A π))
  intro s _hs
  obtain ⟨t, ht, he⟩ := hP s
  apply Submodule.mem_sup.mpr
  refine ⟨t, ht, s - t, ?_, by abel⟩
  have hk := exactVeroneseDegree_ker A π hne hgen n h d 0
  rw [Nat.zero_add, pow_one] at hk
  rw [← hk, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact he.symm

/-- Homogeneous lifts of the original closed sections generate the full compatible algebra. -/
theorem exactVeronese_subalgebra_eq_top
    (S : Subalgebra (A)
      (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)))
    (hA : ∀ d (s : boundaryIntegralDegree A π n h 0 (exactVeroneseStep A π hne hgen n h * d)),
      ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        DirectSum.of _ d t ∈ S ∧
          compatibleDegreeEval A π n h 0 (exactVeroneseStep A π hne hgen n h * d) t = s) : S =
      ⊤ := by
  have hd (d : ℕ) (s : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) :
      DirectSum.of _ d s ∈ S := by
    let f := DirectSum.lof A ℕ
      (fun i ↦ ↥(compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) i)) d
    have hp : S.toSubmodule.comap f = ⊤ := by
      apply exactVeroneseDegree_submodule_eq_top A π hne hgen n h d
      intro u
      obtain ⟨t, ht, he⟩ := hA d (compatibleDegreeEval A π n h 0
        (exactVeroneseStep A π hne hgen n h * d) u)
      exact ⟨t, ht, he⟩
    exact (show s ∈ S.toSubmodule.comap f from hp ▸ Submodule.mem_top)
  apply top_unique
  intro s _hs
  clear _hs
  induction s using DirectSum.induction_on with
  | zero => exact S.zero_mem
  | of d s => exact hd d s
  | add s t hs ht => exact S.add_mem hs ht

/-- A fixed finite family whose algebra lifts every closed homogeneous piece generates globally. -/
theorem exactVeronese_finiteType_of_closed_generators
    (T : Finset (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)))
    (hT : ∀ d (s : boundaryIntegralDegree A π n h 0 (exactVeroneseStep A π hne hgen n h * d)),
      ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        (DirectSum.of _ d t :
          CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) ∈
            Algebra.adjoin A (T : Set _) ∧
          compatibleDegreeEval A π n h 0 (exactVeroneseStep A π hne hgen n h * d) t = s) :
    Algebra.FiniteType (A)
      (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) :=
  ⟨⟨T, exactVeronese_subalgebra_eq_top A π hne hgen n h _ hT⟩⟩

end FLT.Mazur.PolygonArithmeticStages
