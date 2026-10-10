/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Sections of separated unramified morphisms

A section of a separated unramified morphism is both open and closed. The
open assertion follows by pulling back the open diagonal, without reducedness
or a hypothesis on the base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UnramifiedSectionImmersion

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include hs

/-- A section of an unramified morphism is an open immersion over arbitrary bases. -/
theorem isOpenImmersion [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion s := by
  let _ : MorphismProperty.HasOfPostcompProperty
      @IsOpenImmersion.{u} (@LocallyOfFiniteType.{u} ⊓ @FormallyUnramified.{u}) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y g ⟨hft, hfu⟩
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal g))
  have : IsOpenImmersion (s ≫ f) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion.{u})
    (W' := @LocallyOfFiniteType.{u} ⊓ @FormallyUnramified.{u}) s f ⟨inferInstance, inferInstance⟩
    inferInstance

/-- Separatedness makes the same section a closed immersion. -/
theorem isClosedImmersion [IsSeparated f] : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s f

end FLT.Mazur.UnramifiedSectionImmersion
