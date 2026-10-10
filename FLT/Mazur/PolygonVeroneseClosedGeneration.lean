/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseDegreeFinite
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

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Generating the actual closed-stage image suffices to generate the whole compatible degree. -/
theorem exactVeroneseDegree_submodule_eq_top (d : ℕ)
    (P : Submodule (PowerSeries K)
      (compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d))
    (hP : ∀ s, ∃ t ∈ P,
      compatibleDegreeEval K n h 0 (exactVeroneseStep K n h * d) t =
        compatibleDegreeEval K n h 0 (exactVeroneseStep K n h * d) s) : P = ⊤ := by
  let _ := exactVeroneseDegree_finite K n h d
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsAdicComplete.le_jacobson_bot (parameterIdeal K))
  intro s _hs
  obtain ⟨t, ht, he⟩ := hP s
  apply Submodule.mem_sup.mpr
  refine ⟨t, ht, s - t, ?_, by abel⟩
  have hk := exactVeroneseDegree_ker K n h d 0
  rw [Nat.zero_add, pow_one] at hk
  rw [← hk, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact he.symm

/-- Homogeneous lifts of the original closed sections generate the full compatible algebra. -/
theorem exactVeronese_subalgebra_eq_top
    (A : Subalgebra (PowerSeries K)
      (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)))
    (hA : ∀ d (s : boundarySeriesDegree K n h 0 (exactVeroneseStep K n h * d)),
      ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        DirectSum.of _ d t ∈ A ∧
          compatibleDegreeEval K n h 0 (exactVeroneseStep K n h * d) t = s) : A = ⊤ := by
  have hd (d : ℕ) (s : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) :
      DirectSum.of _ d s ∈ A := by
    let f := DirectSum.lof (PowerSeries K) ℕ
      (fun i ↦ ↥(compatibleVeroneseDegree K n h (exactVeroneseStep K n h) i)) d
    have hp : A.toSubmodule.comap f = ⊤ := by
      apply exactVeroneseDegree_submodule_eq_top K n h d
      intro u
      obtain ⟨t, ht, he⟩ := hA d (compatibleDegreeEval K n h 0
        (exactVeroneseStep K n h * d) u)
      exact ⟨t, ht, he⟩
    exact (show s ∈ A.toSubmodule.comap f from hp ▸ Submodule.mem_top)
  apply top_unique
  intro s _hs
  clear _hs
  induction s using DirectSum.induction_on with
  | zero => exact A.zero_mem
  | of d s => exact hd d s
  | add s t hs ht => exact A.add_mem hs ht

/-- A fixed finite family whose algebra lifts every closed homogeneous piece generates globally. -/
theorem exactVeronese_finiteType_of_closed_generators
    (T : Finset (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)))
    (hT : ∀ d (s : boundarySeriesDegree K n h 0 (exactVeroneseStep K n h * d)),
      ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        (DirectSum.of _ d t :
          CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) ∈
            Algebra.adjoin (PowerSeries K) (T : Set _) ∧
          compatibleDegreeEval K n h 0 (exactVeroneseStep K n h * d) t = s) :
    Algebra.FiniteType (PowerSeries K)
      (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) :=
  ⟨⟨T, exactVeronese_subalgebra_eq_top K n h _ hT⟩⟩

end FLT.Mazur.PolygonInfinitesimalStages
