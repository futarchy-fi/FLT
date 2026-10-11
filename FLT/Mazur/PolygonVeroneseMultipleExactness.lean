/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseDegreeFinite

/-!
# Exact reduction for every multiple of the chosen Veronese step

Passing to a common multiple retains the original evaluation, its parameter-power
kernel, and finiteness and completeness of each homogeneous module.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (q : ℕ) (hq : exactVeroneseStep K n h ∣ q)

include hq

/-- Evaluation in every multiple of the exact step is the original surjective evaluation. -/
theorem multipleVeroneseDegree_surjective (d m : ℕ) :
    Function.Surjective (compatibleDegreeEval K n h m (q * d)) := by
  obtain ⟨r, rfl⟩ := hq
  rw [Nat.mul_assoc]
  exact exactVeroneseDegree_surjective K n h (r * d) m

/-- Passing to a multiple retains the actual parameter-power kernel. -/
theorem multipleVeroneseDegree_kernel (d m : ℕ)
    (s : compatibleVeroneseDegree K n h q d) :
    compatibleDegreeEval K n h m (q * d) s = 0 ↔
      ∃ t : compatibleVeroneseDegree K n h q d,
        (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s := by
  revert s
  obtain ⟨r, rfl⟩ := hq
  change ∀ s : compatibleSectionDegree K n h (exactVeroneseStep K n h * r * d),
    compatibleDegreeEval K n h m (exactVeroneseStep K n h * r * d) s = 0 ↔
      ∃ t : compatibleSectionDegree K n h (exactVeroneseStep K n h * r * d),
        (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s
  rw [Nat.mul_assoc]
  exact exactVeroneseDegree_kernel K n h (r * d) m

/-- Every common retained degree remains finite over the original complete coefficient ring. -/
theorem multipleVeroneseDegree_finite (d : ℕ) : Module.Finite (PowerSeries K)
    (compatibleVeroneseDegree K n h q d) := by
  obtain ⟨r, rfl⟩ := hq
  unfold compatibleVeroneseDegree
  rw [Nat.mul_assoc]
  exact exactVeroneseDegree_finite K n h (r * d)

/-- The original parameter-adic completeness persists under passage to a multiple. -/
theorem multipleVeroneseDegree_complete (d : ℕ) : IsAdicComplete (parameterIdeal K)
    (compatibleVeroneseDegree K n h q d) := by
  obtain ⟨r, rfl⟩ := hq
  unfold compatibleVeroneseDegree
  rw [Nat.mul_assoc]
  exact exactVeroneseDegree_complete K n h (r * d)

end FLT.Mazur.PolygonInfinitesimalStages
