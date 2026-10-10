/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryFullNormalizedMarking
public import FLT.Mazur.GroupTorsionTransport
public import FLT.Mazur.GroupTorsionBaseChange

/-!
# The original full torsion basis on the normalized auxiliary cubic

Pull back the original sixteen-section scheme isomorphism along the actual
auxiliary family. The coefficient and normalization group isomorphisms then
carry the entire torsion equalizer to the normalized cubic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ levelFour.left)

/-- The iterated auxiliary torsion pullback is the actual coefficient torsion pullback. -/
def auxiliaryFamilyTorsionPullbackIso :
    (Over.pullback f).obj (Over.mk auxiliaryFourTorsionMap) ≅
      (Over.pullback (auxiliaryCoefficientBase (auxiliaryPointSections f))).obj fourTorsion :=
  (Over.pullbackComp f levelFour.hom).symm.app fourTorsion ≪≫
    eqToIso (congrArg (fun k => (Over.pullback k).obj fourTorsion)
      (auxiliaryPointSections_base f).symm)

/-- The original full basis identifies the torsion equalizer of the coefficient pullback group. -/
def auxiliaryFamilyCoefficientTorsionBasis :
    (Over.pullback f).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      GroupTorsionScheme.scheme
        (auxiliaryUniversalPullbackGroup (auxiliaryPointSections f)).X 4 :=
  auxiliaryBaseChangedFullBasis f ≪≫ auxiliaryFamilyTorsionPullbackIso f ≪≫
    GroupTorsionScheme.baseChangeIso
      (auxiliaryCoefficientBase (auxiliaryPointSections f)) universalGroup 4

attribute [local irreducible] auxiliaryPullbackGroup auxiliaryNormalizedGroup
  auxiliaryNormalizationGroupIso auxiliaryCoefficientGroupIso

/-- The original complete basis identifies the full torsion scheme on the auxiliary cubic. -/
def auxiliaryFamilyPullbackTorsionBasis :
    (Over.pullback f).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      GroupTorsionScheme.scheme (auxiliaryPullbackGroup (auxiliaryPointSections f)).X 4 :=
  auxiliaryFamilyCoefficientTorsionBasis f ≪≫
    GroupTorsionScheme.transportIso
      (auxiliaryUniversalPullbackGroup (auxiliaryPointSections f))
      (auxiliaryPullbackGroup (auxiliaryPointSections f))
      (auxiliaryCoefficientGroupIso (auxiliaryPointSections f)).symm 4

/-- Normalization retains the entire original sixteen-section torsion-basis scheme. -/
def auxiliaryFamilyNormalizedTorsionBasis :
    (Over.pullback f).obj (Over.mk auxiliaryConstantLabelsMap) ≅
      GroupTorsionScheme.scheme (auxiliaryNormalizedGroup (auxiliaryPointSections f)).X 4 :=
  auxiliaryFamilyPullbackTorsionBasis f ≪≫
    GroupTorsionScheme.transportIso (auxiliaryPullbackGroup (auxiliaryPointSections f))
      (auxiliaryNormalizedGroup (auxiliaryPointSections f))
      (auxiliaryNormalizationGroupIso (auxiliaryPointSections f)).symm 4

end FLT.Mazur.UniversalWeierstrass
