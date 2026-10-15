/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticDegreeFinite
public import FLT.Mazur.PolygonVeroneseBoundedGenerators

/-!
# Finite generators covering bounded compatible degrees

Each original compatible homogeneous module is finite over the complete
base. A finite sum of their images has a finite spanning family, whose
algebra therefore contains every compatible section in the specified range.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n] [IsAdicComplete (ideal A π) A]

/-- One finite family contains every original compatible section in bounded retained degrees. -/
theorem exactVeronese_bounded_generators (B : ℕ) :
    ∃ T : Finset (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)),
      ∀ d < B, ∀ s : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        (DirectSum.of _ d s :
          CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) ∈
            Algebra.adjoin A (T : Set _) := by
  let f (d : ℕ) := DirectSum.lof A ℕ
    (fun i ↦ ↥(compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) i)) d
  let _ (d : Fin B) := exactVeroneseDegree_finite A π hne hgen n h d
  obtain ⟨T, hT⟩ := PolygonInfinitesimalStages.finiteModuleImages_in_adjoin (fun d : Fin B ↦ f d)
  exact ⟨T, fun d hd s ↦ hT ⟨d, hd⟩ s⟩

end FLT.Mazur.PolygonArithmeticStages
