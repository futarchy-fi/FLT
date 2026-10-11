/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedMarkingSections

/-!
# A sealed form of the actual auxiliary normalization group isomorphism

Keep the existing group comparison opaque during further base changes. Its
identity with the original comparison and its full marking equation are
retained explicitly, without expanding the geometric group operations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The unchanged normalization group isomorphism, sealed for further specialization. -/
irreducible_def auxiliarySealedNormalizationGroupIso :
    auxiliaryNormalizedGroup g ≅ auxiliaryPullbackGroup g := auxiliaryNormalizationGroupIso g

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso auxiliaryCoefficientGroupIso

/-- The original normalized full marking returns to the unchanged original full marking. -/
theorem auxiliaryFullNormalizedMarking_compare {T : Over (Spec (.of R))}
    (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour) (a : Labels 4) :
    auxiliaryFullNormalizedMarking g p a ≫
      (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom =
        auxiliaryFullPullbackMarking g p a := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, auxiliaryFullNormalizedMarking_left, Category.assoc]
  have h : (auxiliaryNormalizationGroupIso g).inv.hom.hom.hom.left ≫
      (auxiliaryNormalizationGroupIso g).hom.hom.hom.hom.left = 𝟙 _ :=
    congrArg (fun e => e.hom.hom.hom.left) (auxiliaryNormalizationGroupIso g).inv_hom_id
  rw [h, Category.comp_id]

/-- Sealing the actual normalization retains the full original marking comparison. -/
theorem auxiliarySealedNormalizationGroupIso_marking {T : Over (Spec (.of R))}
    (p : (Over.map (auxiliaryCoefficientBase g)).obj T ⟶ levelFour) (a : Labels 4) :
    auxiliaryFullNormalizedMarking g p a ≫
      (auxiliarySealedNormalizationGroupIso g).hom.hom.hom.hom =
        auxiliaryFullPullbackMarking g p a := by
  rw [auxiliarySealedNormalizationGroupIso_def]
  exact auxiliaryFullNormalizedMarking_compare g p a

end FLT.Mazur.UniversalWeierstrass
