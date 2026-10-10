/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentClosedPushforward
public import FLT.Mazur.IdealAdicRelativeImageOpenCover

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

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf

/-- The original coefficient sheaf transported onto its tensor image open. -/
def relativeImageCoefficientSheaf : (relativeTensorImageOpen J f U).toScheme.Modules :=
  (pushforward (relativeTensorImageIso J f U).hom).obj (relativeChartCoefficientSheaf J f U)

/-- The image-open coefficient sheaf retains local finite presentation. -/
instance relativeImageCoefficientSheaf_isFinitePresentation :
    (relativeImageCoefficientSheaf J f U).IsFinitePresentation :=
  FCurve.CoherentDevissage.coherentPresentation_pushforwardIso (relativeTensorImageIso J f U)
    (relativeChartCoefficientSheaf J f U)

/-- Transport to image opens preserves the original ambient coefficient pushforward. -/
def relativeImageCoefficientPushforwardIso :
    (pushforward (relativeTensorImageOpen J f U).ι).obj (relativeImageCoefficientSheaf J f U) ≅
      (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U) :=
  (pushforwardComp (relativeTensorImageIso J f U).hom (relativeTensorImageOpen J f U).ι).app
      (relativeChartCoefficientSheaf J f U) ≪≫
    (pushforwardCongr (relativeTensorImageIso_hom_ι J f U)).app
      (relativeChartCoefficientSheaf J f U)

/-- Restriction along the image identification recovers the original coefficient sheaf. -/
def relativeImageCoefficientRestrictionIso :
    (restrictFunctor (relativeTensorImageIso J f U).hom).obj
        (relativeImageCoefficientSheaf J f U) ≅ relativeChartCoefficientSheaf J f U :=
  (restrictFunctorAdjCounitIso (relativeTensorImageIso J f U).hom).app
    (relativeChartCoefficientSheaf J f U)

end FLT.Mazur.IdealAdicGradedPullback
