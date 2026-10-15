/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompatibleZero
public import FLT.Mazur.PolygonArithmeticVeronese

/-!
# One positive Veronese with exact reduction in every degree

Combine the uniform positive bounds with the separate degree-zero
coefficient calculation. The resulting single Veronese has surjective
actual evaluations and parameter-power kernels in all its degrees.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

include hne hgen in
/-- One positive step gives actual surjective reductions with exact kernels in every degree. -/
theorem compatibleVeronese_allDegreeExact : ∃ q : ℕ, 0 < q ∧ ∀ d m : ℕ,
    Function.Surjective (compatibleDegreeEval A π n h m (q * d)) ∧
    (∀ s : compatibleVeroneseDegree A π n h q d,
      compatibleDegreeEval A π n h m (q * d) s = 0 ↔
        ∃ t : compatibleVeroneseDegree A π n h q d,
          π ^ (m + 1) • t = s) := by
  obtain ⟨N₀, hA⟩ := compatibleDegree_uniformLifting A π n h hne hgen
  obtain ⟨N₁, hB⟩ := compatibleDegree_uniformKernel A π n h hne hgen
  refine ⟨max N₀ N₁ + 1, Nat.zero_lt_succ _, fun d m ↦ ?_⟩
  by_cases hd : d = 0
  · subst d
    simpa only [Nat.mul_zero, compatibleVeroneseDegree] using
      And.intro (compatibleDegreeEval_zero_surjective A π hne hgen n h m)
        (compatibleDegreeEval_zero_kernel A π hne hgen n h m)
  · have hb : max N₀ N₁ ≤ (max N₀ N₁ + 1) * d :=
      le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hd))
    refine ⟨?_, hB _ (le_trans (le_max_right _ _) hb) m⟩
    intro s
    obtain ⟨t, ht⟩ := hA _ (le_trans (le_max_left _ _) hb) m s
    exact ⟨t, Subtype.ext ht⟩

/-- A fixed positive step chosen from the proved simultaneous bounds. -/
def exactVeroneseStep : ℕ := (compatibleVeronese_allDegreeExact A π hne hgen n h).choose

include hne hgen in
/-- The chosen step is positive, so original homogeneous degrees remain distinct. -/
theorem exactVeroneseStep_pos : 0 < exactVeroneseStep A π hne hgen n h :=
  (compatibleVeronese_allDegreeExact A π hne hgen n h).choose_spec.1

include hne hgen in
/-- Every retained degree has surjective actual stage evaluation. -/
theorem exactVeroneseDegree_surjective (d m : ℕ) :
    Function.Surjective (compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d)) :=
  ((compatibleVeronese_allDegreeExact A π hne hgen n h).choose_spec.2 d m).1

include hne hgen in
/-- Every retained degree has precisely the original parameter-power evaluation kernel. -/
theorem exactVeroneseDegree_kernel (d m : ℕ)
    (s : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d) :
    compatibleDegreeEval A π n h m (exactVeroneseStep A π hne hgen n h * d) s = 0 ↔
      ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        π ^ (m + 1) • t = s :=
  ((compatibleVeronese_allDegreeExact A π hne hgen n h).choose_spec.2 d m).2 s

end FLT.Mazur.PolygonArithmeticStages
