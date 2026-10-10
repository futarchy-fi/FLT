/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedTorsionBasis
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedParameter

/-!
# The original full torsion basis at the normalized coefficient parameter

The original sixteen-section scheme basis transports through the exact
normalized coefficient group comparison. Inverting the full equalizer
base-change isomorphism recovers the original universal torsion scheme at
that parameter, retaining the complete inclusion diagram.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

attribute [local irreducible] auxiliaryNormalizedGroup auxiliaryNormalizedCoefficientGroupIso

/-- The original complete basis of the normalized coefficient pullback group. -/
def auxiliaryFamilyNormalizedUniversalTorsionBasis :
    (Over.pullback f).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      GroupTorsionScheme.scheme
        (auxiliaryNormalizedUniversalPullbackGroup (auxiliaryPointSections f)).X 4 :=
  auxiliaryFamilyNormalizedTorsionBasis f ≪≫
    GroupTorsionScheme.transportIso (auxiliaryNormalizedGroup (auxiliaryPointSections f))
      (auxiliaryNormalizedUniversalPullbackGroup (auxiliaryPointSections f))
      (auxiliaryNormalizedCoefficientGroupIso (auxiliaryPointSections f)) 4

/-- The full original basis identifies the original universal torsion at the new parameter. -/
def auxiliaryFamilyNormalizedParameterTorsionBasis :
    (Over.pullback f).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      (Over.pullback (auxiliaryNormalizedCoefficientBase (auxiliaryPointSections f))).obj
        fourTorsion :=
  auxiliaryFamilyNormalizedUniversalTorsionBasis f ≪≫
    (GroupTorsionScheme.baseChangeIso
      (auxiliaryNormalizedCoefficientBase (auxiliaryPointSections f)) universalGroup 4).symm

/-- The full basis comparison retains the original normalized group map on scheme inclusions. -/
@[reassoc] theorem auxiliaryFamilyNormalizedUniversalTorsionBasis_inclusion_left :
    (auxiliaryFamilyNormalizedUniversalTorsionBasis f).hom.left ≫
      (GroupTorsionScheme.inclusion
        (auxiliaryNormalizedUniversalPullbackGroup (auxiliaryPointSections f)).X 4).left =
          (auxiliaryFamilyNormalizedTorsionBasis f).hom.left ≫
            (GroupTorsionScheme.inclusion
              (auxiliaryNormalizedGroup (auxiliaryPointSections f)).X 4).left ≫
                (auxiliaryNormalizedCoefficientGroupIso
                  (auxiliaryPointSections f)).hom.hom.hom.hom.left := by
  rw [auxiliaryFamilyNormalizedUniversalTorsionBasis, Iso.trans_hom, Over.comp_left, Category.assoc]
  exact congrArg (fun k => (auxiliaryFamilyNormalizedTorsionBasis f).hom.left ≫ k)
    (congrArg Over.Hom.left (GroupTorsionScheme.transport_inclusion
      (auxiliaryNormalizedGroup (auxiliaryPointSections f))
      (auxiliaryNormalizedUniversalPullbackGroup (auxiliaryPointSections f))
      (auxiliaryNormalizedCoefficientGroupIso (auxiliaryPointSections f)) 4))

end FLT.Mazur.UniversalWeierstrass
