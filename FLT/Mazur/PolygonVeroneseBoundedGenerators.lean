/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseDegreeFinite

/-!
# Finite generators covering bounded compatible degrees

Each original compatible homogeneous module is finite over the complete
base. A finite sum of their images has a finite spanning family, whose
algebra therefore contains every compatible section in the specified range.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

/-- Finitely many finite module images lie in one finitely generated subalgebra. -/
theorem finiteModuleImages_in_adjoin {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {I : Type*} [Finite I] {M : I → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] A) :
    ∃ T : Finset A, ∀ i s, f i s ∈ Algebra.adjoin R (T : Set A) := by
  obtain ⟨T, hT⟩ := Submodule.fg_iSup (fun i ↦ LinearMap.range (f i))
    (fun i ↦ Submodule.fg_range (f i))
  refine ⟨T, fun i s ↦ ?_⟩
  have hm : f i s ∈ Submodule.span R (T : Set A) := by
    rw [hT]
    exact (le_iSup (fun i ↦ LinearMap.range (f i)) i) ⟨s, rfl⟩
  exact Algebra.span_le_adjoin R (T : Set A) hm

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- One finite family contains every original compatible section in bounded retained degrees. -/
theorem exactVeronese_bounded_generators (B : ℕ) :
    ∃ T : Finset (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)),
      ∀ d < B, ∀ s : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        (DirectSum.of _ d s :
          CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) ∈
            Algebra.adjoin (PowerSeries K) (T : Set _) := by
  let f (d : ℕ) := DirectSum.lof (PowerSeries K) ℕ
    (fun i ↦ ↥(compatibleVeroneseDegree K n h (exactVeroneseStep K n h) i)) d
  let _ (d : Fin B) := exactVeroneseDegree_finite K n h d
  obtain ⟨T, hT⟩ := finiteModuleImages_in_adjoin (fun d : Fin B ↦ f d)
  exact ⟨T, fun d hd s ↦ hT ⟨d, hd⟩ s⟩

end FLT.Mazur.PolygonInfinitesimalStages
