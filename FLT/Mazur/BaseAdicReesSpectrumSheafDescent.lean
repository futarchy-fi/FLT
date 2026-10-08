/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentOpenDescent
public import FLT.Mazur.BaseAdicReesSpectrumImageSheafCocycle
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

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

attribute [local instance] spectrumSpaceMap_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf
attribute [local irreducible] spectrumImageSheaf spectrumImageSheafTransition

/-- The actual coefficient modules and transitions form module-sheaf gluing data. -/
def spectrumSheafGluingData : ModuleSheafGluing.Data (spectrumImageOpen f J) :=
  ModuleSheafGluing.ofLocalEval (spectrumImageOpen f J)
    (spectrumImageSheaf f J M) (spectrumImageSheafTransition f J M)
    (spectrumImageSheafTransition_cocycle f J M)

/-- The coefficient module descended to the whole changed-base scheme. -/
def spectrumDescendedSheaf : (relativeSpace f J).Modules :=
  (spectrumSheafGluingData f J M).glued

/-- Restriction of the descended coefficient sheaf recovers each image-open module. -/
def spectrumDescendedSheafRestrictionIso (U : X.affineOpens) :
    (spectrumDescendedSheaf f J M).restrict (spectrumImageOpen f J U).ι ≅
      spectrumImageSheaf f J M U :=
  (spectrumSheafGluingData f J M).restrictionIso U

/-- Local finite presentations on the tensor charts descend globally. -/
instance spectrumDescendedSheaf_isFinitePresentation [IsNoetherianRing R] :
    (spectrumDescendedSheaf f J M).IsFinitePresentation := by
  apply FCurve.coherent_of_openCover (spectrumDescendedSheaf f J M)
    (spectrumImageOpen f J) (iSup_spectrumImageOpen f J)
  intro U
  exact (SheafOfModules.isFinitePresentation
    (spectrumImageOpen f J U).toScheme.ringCatSheaf).prop_of_iso
    (spectrumDescendedSheafRestrictionIso f J M U).symm
    (inferInstanceAs (spectrumImageSheaf f J M U).IsFinitePresentation)

/-- The descended module has its canonical map to each original ambient chart module. -/
def spectrumDescendedSheafProjection (U : X.affineOpens) :
    spectrumDescendedSheaf f J M ⟶ spectrumAmbientSheaf f J M U :=
  (spectrumSheafGluingData f J M).projection U ≫
    (spectrumImageSheafPushforwardIso f J M U).hom

/-- Restriction along each original tensor chart recovers its coefficient sheaf. -/
def spectrumDescendedSheafChartIso (U : X.affineOpens) :
    (spectrumDescendedSheaf f J M).restrict (spectrumSpaceMap f J U) ≅
      spectrumSheaf f J M U :=
  (restrictFunctorCongr (spectrumImageIso_hom_ι f J U)).symm.app
      (spectrumDescendedSheaf f J M) ≪≫
    (restrictFunctorComp (spectrumImageIso f J U).hom
      (spectrumImageOpen f J U).ι).app (spectrumDescendedSheaf f J M) ≪≫
    (restrictFunctor (spectrumImageIso f J U).hom).mapIso
      (spectrumDescendedSheafRestrictionIso f J M U) ≪≫
    spectrumImageSheafRestrictionIso f J M U

end FLT.Mazur.BaseAdicRees
