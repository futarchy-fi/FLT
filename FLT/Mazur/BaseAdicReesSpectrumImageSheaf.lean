/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentClosedPushforward
public import FLT.Mazur.BaseAdicReesSpectrumImageOpenCover

/-!
# Coefficient modules on the image-open cover

Transport the original affine coefficient sheaves to image opens without
changing their ambient pushforwards. Local finite presentation is retained.
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
  (J : Ideal R) [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation] (U : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback spectrumSheaf

/-- The fixed presentation retains finite presentation of the original model sheaf. -/
instance spectrumSheaf_isFinitePresentation [IsNoetherianRing R] :
    (spectrumSheaf f J M U).IsFinitePresentation := by
  unfold spectrumSheaf modelSpectrum
  exact modelSheaf_isFinitePresentation f J U M

/-- The original coefficient sheaf transported onto its tensor image open. -/
def spectrumImageSheaf : (spectrumImageOpen f J U).toScheme.Modules :=
  (pushforward (spectrumImageIso f J U).hom).obj (spectrumSheaf f J M U)

/-- The image-open coefficient sheaf retains local finite presentation. -/
instance spectrumImageSheaf_isFinitePresentation [IsNoetherianRing R] :
    (spectrumImageSheaf f J M U).IsFinitePresentation :=
  FCurve.CoherentDevissage.coherentPresentation_pushforwardIso (spectrumImageIso f J U)
    (spectrumSheaf f J M U)

/-- Transport to image opens preserves the original ambient coefficient pushforward. -/
def spectrumImageSheafPushforwardIso :
    (pushforward (spectrumImageOpen f J U).ι).obj (spectrumImageSheaf f J M U) ≅
      (pushforward (spectrumSpaceMap f J U)).obj (spectrumSheaf f J M U) :=
  (pushforwardComp (spectrumImageIso f J U).hom (spectrumImageOpen f J U).ι).app
      (spectrumSheaf f J M U) ≪≫
    (pushforwardCongr (spectrumImageIso_hom_ι f J U)).app
      (spectrumSheaf f J M U)

/-- Restriction along the image identification recovers the original coefficient sheaf. -/
def spectrumImageSheafRestrictionIso :
    (restrictFunctor (spectrumImageIso f J U).hom).obj
        (spectrumImageSheaf f J M U) ≅ spectrumSheaf f J M U :=
  (restrictFunctorAdjCounitIso (spectrumImageIso f J U).hom).app
    (spectrumSheaf f J M U)

end FLT.Mazur.BaseAdicRees
