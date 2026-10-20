/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyCover
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Smoothness descends along an actual fppf covering family

Collapse the family to its surjective flat coproduct morphism. Smoothness
upstairs is checked on the original summands, then fppf descent applies.
No finite subcover or quasi-compactness of the covering maps is needed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{u}} (f : X ⟶ S) (C : Scheme.Cover.{u} Scheme.fppfPrecoverage S)

/-- Smoothness of every member's pullback implies smoothness over the coproduct cover. -/
theorem smooth_pullback_projection (h : ∀ i, Smooth (pullback.snd f (C.f i))) :
    Smooth (pullback.snd f (projection C)) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Smooth) (sigmaOpenCover C.X)
  intro i
  change Smooth (pullback.snd (pullback.snd f (projection C)) (Sigma.ι C.X i))
  rw [← pullbackLeftPullbackSndIso_hom_snd f (projection C) (Sigma.ι C.X i)]
  have hs : Smooth (pullback.snd f (Sigma.ι C.X i ≫ projection C)) := by
    rw [inclusion_projection]
    exact h i
  let _ := hs
  infer_instance

/-- Smoothness descends from all original members of an arbitrary small fppf family. -/
theorem smooth_of_cover (h : ∀ i, Smooth (pullback.snd f (C.f i))) : Smooth f :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (smooth_pullback_projection f C h)

/-- The family detects smoothness in both directions. -/
theorem smooth_iff_cover : Smooth f ↔ ∀ i, Smooth (pullback.snd f (C.f i)) := by
  constructor
  · intro h i
    let _ := h
    infer_instance
  · exact smooth_of_cover f C

end FLT.Mazur.SchemeFppfFamily
