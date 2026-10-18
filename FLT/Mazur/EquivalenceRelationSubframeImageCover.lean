/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeImage
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Faithfully flat strict selections onto their actual image

Restricting the target to the constructed open image makes every selected
subframe map an etale surjection. Consequently regular functions descend
uniquely along its genuine scheme kernel pair. No binomial degree is inverted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (ι : J ↪ I)

/-- Every original point maps to the constructed target image. -/
theorem subframeImage_domain : U ≤ subframeMap e o o' ι ⁻¹ᵁ subframeImageOpen e o o' U ι :=
  fun x hx ↦ ⟨x, hx, rfl⟩

/-- The actual selection, with codomain restricted to its image open. -/
def subframeImageCover : U.toScheme ⟶ (subframeImageOpen e o o' U ι).toScheme :=
  subframeRefinementMap e o o' ι U _ (subframeImage_domain e o o' U ι)

/-- The cover retains the unchanged ambient subframe selection. -/
@[reassoc] theorem subframeImageCover_inclusion :
    subframeImageCover e o o' U ι ≫ (subframeImageOpen e o o' U ι).ι =
      U.ι ≫ subframeMap e o o' ι := subframeRefinementMap_inclusion _ _ _ _ _ _ _

/-- Target restriction preserves the etale selection geometry. -/
instance subframeImageCover_etale : Etale (subframeImageCover e o o' U ι) :=
  subframeRefinementMap_etale _ _ _ _ _ _ _

/-- Each actual target image point has a preimage in the whole original source chart. -/
instance subframeImageCover_surjective : Surjective (subframeImageCover e o o' U ι) := by
  constructor
  intro y
  obtain ⟨x, hx, he⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact (Scheme.Hom.coe_resLE_apply _ _ _).trans he

/-- Actual selected pullback detects equality of functions on the image target. -/
theorem subframeImageCover_appTop_injective :
    Function.Injective (subframeImageCover e o o' U ι).appTop :=
  SchemeEffectiveEpiSections.appTop_injective _

/-- Descent uses the full scheme kernel pair, retaining all nilpotent structure. -/
theorem subframeImageCover_sections_existsUnique (u : Γ(U.toScheme, ⊤))
    (hu : (pullback.fst (subframeImageCover e o o' U ι)
        (subframeImageCover e o o' U ι)).appTop u =
      (pullback.snd (subframeImageCover e o o' U ι)
        (subframeImageCover e o o' U ι)).appTop u) :
    ∃! v : Γ((subframeImageOpen e o o' U ι).toScheme, ⊤),
      (subframeImageCover e o o' U ι).appTop v = u :=
  SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback _ _) u hu

end FLT.Mazur.EquivalenceRelationNormalizedFrames
