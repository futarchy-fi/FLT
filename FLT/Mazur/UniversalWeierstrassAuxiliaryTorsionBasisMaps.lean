/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedTorsionBasis

/-!
# Actual scheme maps of the transported auxiliary torsion bases

The full basis isomorphisms retain both original group comparison maps after
inclusion in the cubic. Projecting to scheme maps avoids unfolding the
bundled group laws while preserving the entire torsion scheme diagram.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso auxiliaryCoefficientGroupIso

/-- The full pulled-back basis retains the actual inverse coefficient group map. -/
@[reassoc] theorem auxiliaryFamilyPullbackTorsionBasis_inclusion_left :
    (auxiliaryFamilyPullbackTorsionBasis f).hom.left ≫
      (GroupTorsionScheme.inclusion (auxiliaryPullbackGroup (auxiliaryPointSections f)).X 4).left =
        (auxiliaryFamilyCoefficientTorsionBasis f).hom.left ≫
          (GroupTorsionScheme.inclusion
            (auxiliaryUniversalPullbackGroup (auxiliaryPointSections f)).X 4).left ≫
              (auxiliaryCoefficientGroupIso (auxiliaryPointSections f)).inv.hom.hom.hom.left := by
  rw [auxiliaryFamilyPullbackTorsionBasis, Iso.trans_hom, Over.comp_left, Category.assoc]
  exact congrArg (fun k => (auxiliaryFamilyCoefficientTorsionBasis f).hom.left ≫ k)
    (congrArg Over.Hom.left (GroupTorsionScheme.transport_inclusion
      (auxiliaryUniversalPullbackGroup (auxiliaryPointSections f))
      (auxiliaryPullbackGroup (auxiliaryPointSections f))
      (auxiliaryCoefficientGroupIso (auxiliaryPointSections f)).symm 4))

/-- The full normalized basis retains the actual inverse normalization group map. -/
@[reassoc] theorem auxiliaryFamilyNormalizedTorsionBasis_inclusion_left :
    (auxiliaryFamilyNormalizedTorsionBasis f).hom.left ≫
      (GroupTorsionScheme.inclusion
        (auxiliaryNormalizedGroup (auxiliaryPointSections f)).X 4).left =
        (auxiliaryFamilyPullbackTorsionBasis f).hom.left ≫
          (GroupTorsionScheme.inclusion
            (auxiliaryPullbackGroup (auxiliaryPointSections f)).X 4).left ≫
            (auxiliaryNormalizationGroupIso (auxiliaryPointSections f)).inv.hom.hom.hom.left := by
  rw [auxiliaryFamilyNormalizedTorsionBasis, Iso.trans_hom, Over.comp_left, Category.assoc]
  exact congrArg (fun k => (auxiliaryFamilyPullbackTorsionBasis f).hom.left ≫ k)
    (congrArg Over.Hom.left (GroupTorsionScheme.transport_inclusion
      (auxiliaryPullbackGroup (auxiliaryPointSections f))
      (auxiliaryNormalizedGroup (auxiliaryPointSections f))
      (auxiliaryNormalizationGroupIso (auxiliaryPointSections f)).symm 4))

end FLT.Mazur.UniversalWeierstrass
