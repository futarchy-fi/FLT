/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentOpenDescent
public import FLT.Mazur.IdealAdicRelativeImageCoefficientCocycle
public import FLT.Mazur.ModuleSheafEvaluatedGluing

/-!
# Descent of the relative coefficient sheaf

The actual image-open coefficient transitions define gluing data. Their
glued module sheaf recovers every image chart and is locally finitely presented.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeImageCoefficientSheaf relativeImageCoefficientTransition

/-- The actual coefficient modules and transitions form module-sheaf gluing data. -/
def relativeCoefficientGluingData : ModuleSheafGluing.Data (relativeTensorImageOpen J f) :=
  ModuleSheafGluing.ofLocalEval (relativeTensorImageOpen J f)
    (relativeImageCoefficientSheaf J f) (relativeImageCoefficientTransition J f)
    (relativeImageCoefficientTransition_cocycle J f)

/-- The coefficient module descended to the whole changed-base scheme. -/
def relativeDescendedCoefficientSheaf : (relativeScheme J f).Modules :=
  (relativeCoefficientGluingData J f).glued

/-- Restriction of the descended coefficient sheaf recovers each image-open module. -/
def relativeDescendedCoefficientRestrictionIso (U : X.affineOpens) :
    (relativeDescendedCoefficientSheaf J f).restrict (relativeTensorImageOpen J f U).ι ≅
      relativeImageCoefficientSheaf J f U :=
  (relativeCoefficientGluingData J f).restrictionIso U

/-- Local finite presentations on the tensor charts descend globally. -/
instance relativeDescendedCoefficientSheaf_isFinitePresentation :
    (relativeDescendedCoefficientSheaf J f).IsFinitePresentation := by
  apply FCurve.coherent_of_openCover (relativeDescendedCoefficientSheaf J f)
    (relativeTensorImageOpen J f) (iSup_relativeTensorImageOpen J f)
  intro U
  exact (SheafOfModules.isFinitePresentation
    (relativeTensorImageOpen J f U).toScheme.ringCatSheaf).prop_of_iso
    (relativeDescendedCoefficientRestrictionIso J f U).symm
    (inferInstanceAs (relativeImageCoefficientSheaf J f U).IsFinitePresentation)

/-- The descended module has its canonical map to each original ambient chart module. -/
def relativeDescendedCoefficientProjection (U : X.affineOpens) :
    relativeDescendedCoefficientSheaf J f ⟶ relativeAmbientCoefficient J f U :=
  (relativeCoefficientGluingData J f).projection U ≫
    (relativeImageCoefficientPushforwardIso J f U).hom

/-- Restriction along each original tensor chart recovers its coefficient sheaf. -/
def relativeDescendedCoefficientChartIso (U : X.affineOpens) :
    (relativeDescendedCoefficientSheaf J f).restrict (relativeTensorChart J f U) ≅
      relativeChartCoefficientSheaf J f U :=
  (restrictFunctorCongr (relativeTensorImageIso_hom_ι J f U)).symm.app
      (relativeDescendedCoefficientSheaf J f) ≪≫
    (restrictFunctorComp (relativeTensorImageIso J f U).hom
      (relativeTensorImageOpen J f U).ι).app (relativeDescendedCoefficientSheaf J f) ≪≫
    (restrictFunctor (relativeTensorImageIso J f U).hom).mapIso
      (relativeDescendedCoefficientRestrictionIso J f U) ≪≫
    relativeImageCoefficientRestrictionIso J f U

end FLT.Mazur.IdealAdicGradedPullback
