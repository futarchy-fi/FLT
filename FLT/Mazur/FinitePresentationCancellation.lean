/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Cancelling a locally finite type target from finite presentation

If a composite is locally of finite presentation and its second map is
locally of finite type, its first map is locally of finite presentation.
Compatible affine neighborhoods reduce this to the ring cancellation theorem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FinitePresentationCancellation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Cancel a locally finite type second morphism from a finitely presented composite. -/
theorem of_comp [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).left).mpr
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ g ⁻¹ᵁ W from hxW) (g ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).isOpen
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, ?_⟩
  apply RingHom.FinitePresentation.of_comp_finiteType (g.appLE W U hUW).hom
  · change ((g.appLE W U hUW) ≫ (f.appLE U V hVU)).hom.FinitePresentation
    rw [Scheme.Hom.appLE_comp_appLE]
    exact (f ≫ g).finitePresentation_appLE hW hV _
  · exact g.finiteType_appLE hW hU hUW

end FLT.Mazur.FinitePresentationCancellation
