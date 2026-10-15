/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleSectionCoverNeighborhood

/-!
# Spreading an original open condition from a whole finite fiber

A finite projection sends the complement of the required original open to
a closed set. Its complement supplies an affine base neighborhood on whose
entire inverse image the original map lifts. No reducedness or splitting is
required, and the original source is restricted by actual base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFiberOriginalOpenSpread
universe u
set_option backward.isDefEq.respectTransparency false
variable {E U X Z : Scheme.{u}} (p : E ⟶ U) [IsFinite p]
  (g : E ⟶ X) (j : Z ⟶ X) [IsOpenImmersion j]

/-- An original open condition on a finite fiber holds on the whole inverse-image neighborhood. -/
theorem exists_affine_lift (y : U)
    (hy : ∀ x : E, p x = y → g x ∈ Set.range j) :
    ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧
      ∃ a : (p ⁻¹ᵁ W).toScheme ⟶ Z, a ≫ j = (p ⁻¹ᵁ W).ι ≫ g := by
  let O := g ⁻¹ᵁ j.opensRange
  let B := SchemeOpenEnvelope.fullFiberOpen p O p.isClosedMap
  have hyB : y ∈ B := by
    apply (SchemeOpenEnvelope.mem_fullFiberLocus p O y).mpr
    exact hy
  obtain ⟨W, hW, hyW, hWB⟩ := exists_isAffineOpen_mem_and_subset hyB
  have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ g) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact SchemeOpenEnvelope.preimage_fullFiberOpen_le p O p.isClosedMap
      (hWB x.property)
  exact ⟨W, hW, hyW, IsOpenImmersion.lift j _ hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- Covering the distinguished fiber by actual sections reduces the condition to branch points. -/
theorem exists_affine_lift_of_sections {ι : Type*} (s : ι → (U ⟶ E)) (y : U)
    (hc : ∀ x : E, p x = y → ∃ i, s i y = x)
    (h : ∀ i, g (s i y) ∈ Set.range j) :
    ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧
      ∃ a : (p ⁻¹ᵁ W).toScheme ⟶ Z, a ≫ j = (p ⁻¹ᵁ W).ι ≫ g := by
  apply exists_affine_lift p g j y
  intro x hx
  obtain ⟨i, rfl⟩ := hc x hx
  exact h i

end FLT.Mazur.FiniteFiberOriginalOpenSpread
