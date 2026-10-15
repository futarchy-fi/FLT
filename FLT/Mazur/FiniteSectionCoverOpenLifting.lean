/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleGeometricSectionCover

/-!
# Open conditions detected by a complete section cover

The actual sections of a covering family test whether a whole morphism
factors through an original open immersion. This retains the entire source
scheme and the actual original morphisms, including nilpotent structure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteSectionCoverOpenLifting
universe u
variable {E U X Z : Scheme.{u}} (p : E ⟶ U) {ι : Type*} (s : ι → (U ⟶ E))
  (hc : ∀ x : E, ∃ i, s i (p x) = x) (g : E ⟶ X) (j : Z ⟶ X) [IsOpenImmersion j]

include hc

omit [IsOpenImmersion j] in
/-- A complete section cover detects containment in the original open image. -/
theorem range_subset_iff :
    Set.range g ⊆ Set.range j ↔ ∀ i, Set.range (s i ≫ g) ⊆ Set.range j := by
  constructor
  · intro h i
    rintro _ ⟨y, rfl⟩
    exact h ⟨s i y, rfl⟩
  · intro h
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := hc x
    apply h i
    exact ⟨p x, congrArg g hi⟩

/-- Actual lifts on the sections construct a unique lift of the entire original source. -/
theorem existsUnique_lift (a : ι → (U ⟶ Z)) (ha : ∀ i, a i ≫ j = s i ≫ g) :
    ∃! b : E ⟶ Z, b ≫ j = g ∧ ∀ i, s i ≫ b = a i := by
  have hr : Set.range g ⊆ Set.range j := by
    apply (range_subset_iff p s hc g j).mpr
    intro i
    rw [← ha i]
    rintro _ ⟨y, rfl⟩
    exact ⟨a i y, rfl⟩
  let b := IsOpenImmersion.lift j g hr
  have hb : b ≫ j = g := IsOpenImmersion.lift_fac _ _ _
  refine ⟨b, ⟨hb, fun i ↦ ?_⟩, ?_⟩
  · apply (cancel_mono j).mp
    rw [Category.assoc, hb, ha]
  · intro b' hb'
    exact (cancel_mono j).mp (hb'.1.trans hb.symm)

end FLT.Mazur.FiniteSectionCoverOpenLifting
