/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleDegreeZero
public import FLT.Mazur.PolygonCompatibleVeronese

/-!
# One positive Veronese with exact reduction in every degree

Combine the uniform positive bounds with the separate degree-zero
coefficient calculation. The resulting single Veronese has surjective
actual evaluations and parameter-power kernels in all its degrees.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- One positive step gives actual surjective reductions with exact kernels in every degree. -/
theorem compatibleVeronese_allDegreeExact : ∃ q : ℕ, 0 < q ∧ ∀ d m : ℕ,
    Function.Surjective (compatibleDegreeEval K n h m (q * d)) ∧
    (∀ s : compatibleVeroneseDegree K n h q d,
      compatibleDegreeEval K n h m (q * d) s = 0 ↔
        ∃ t : compatibleVeroneseDegree K n h q d,
          (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s) := by
  obtain ⟨A, hA⟩ := compatibleDegree_uniformLifting K n h
  obtain ⟨B, hB⟩ := compatibleDegree_uniformKernel n h K
  refine ⟨max A B + 1, Nat.zero_lt_succ _, fun d m ↦ ?_⟩
  by_cases hd : d = 0
  · subst d
    simpa only [Nat.mul_zero, compatibleVeroneseDegree] using
      And.intro (compatibleDegreeEval_zero_surjective K n h m)
        (compatibleDegreeEval_zero_kernel K n h m)
  · have hb : max A B ≤ (max A B + 1) * d :=
      le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hd))
    refine ⟨?_, hB _ (le_trans (le_max_right _ _) hb) m⟩
    intro s
    obtain ⟨t, ht⟩ := hA _ (le_trans (le_max_left _ _) hb) m s
    exact ⟨t, Subtype.ext ht⟩

/-- A fixed positive step chosen from the proved simultaneous bounds. -/
def exactVeroneseStep : ℕ := (compatibleVeronese_allDegreeExact K n h).choose

/-- The chosen step is positive, so original homogeneous degrees remain distinct. -/
theorem exactVeroneseStep_pos : 0 < exactVeroneseStep K n h :=
  (compatibleVeronese_allDegreeExact K n h).choose_spec.1

/-- Every retained degree has surjective actual stage evaluation. -/
theorem exactVeroneseDegree_surjective (d m : ℕ) :
    Function.Surjective (compatibleDegreeEval K n h m (exactVeroneseStep K n h * d)) :=
  ((compatibleVeronese_allDegreeExact K n h).choose_spec.2 d m).1

/-- Every retained degree has precisely the original parameter-power evaluation kernel. -/
theorem exactVeroneseDegree_kernel (d m : ℕ)
    (s : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d) :
    compatibleDegreeEval K n h m (exactVeroneseStep K n h * d) s = 0 ↔
      ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        (PowerSeries.X : PowerSeries K) ^ (m + 1) • t = s :=
  ((compatibleVeronese_allDegreeExact K n h).choose_spec.2 d m).2 s

end FLT.Mazur.PolygonInfinitesimalStages
