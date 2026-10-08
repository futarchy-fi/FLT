/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientProjection

/-!
# Section isomorphisms of the descended coefficient projections

The canonical projection is bijective on each subopen of its chart image.
On the whole image it recovers the global sections of the original tensor chart.
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
attribute [local irreducible] relativeChartCoefficientSheaf

/-- The canonical descended projection is bijective on every subopen of its chart. -/
lemma relativeDescendedCoefficientProjection_bijective (U : X.affineOpens)
    (W : (relativeScheme J f).Opens) (hW : W ≤ relativeTensorImageOpen J f U) :
    Function.Bijective ((relativeDescendedCoefficientProjection J f U).app W) := by
  unfold relativeDescendedCoefficientProjection
  change Function.Bijective (fun s ↦
    (relativeImageCoefficientPushforwardIso J f U).hom.app W
      (((relativeCoefficientGluingData J f).projection U).app W s))
  exact (ConcreteCategory.bijective_of_isIso
    ((relativeImageCoefficientPushforwardIso J f U).hom.app W)).comp
    ((relativeCoefficientGluingData J f).projection_bijective U W hW)

/-- The canonical projection as an additive isomorphism on a chart subopen. -/
def relativeDescendedCoefficientProjectionIso (U : X.affineOpens)
    (W : (relativeScheme J f).Opens) (hW : W ≤ relativeTensorImageOpen J f U) :
    Γ(relativeDescendedCoefficientSheaf J f, W) ≅ Γ(relativeAmbientCoefficient J f U, W) := by
  let _ := (ConcreteCategory.isIso_iff_bijective
    ((relativeDescendedCoefficientProjection J f U).app W)).mpr
    (relativeDescendedCoefficientProjection_bijective J f U W hW)
  exact asIso ((relativeDescendedCoefficientProjection J f U).app W)

/-- On the whole image open, the ambient chart pushforward gives chart global sections. -/
def relativeAmbientCoefficientTopIso (U : X.affineOpens) :
    let := closedBaseAlgebra J f U.1
    Γ(relativeAmbientCoefficient J f U, relativeTensorImageOpen J f U) ≅
      Γ(relativeChartCoefficientSheaf J f U, ⊤) := by
  let := closedBaseAlgebra J f U.1
  exact (relativeChartCoefficientSheaf J f U).presheaf.mapIso
    (eqToIso (Scheme.Hom.preimage_opensRange (relativeTensorChart J f U)).symm).op

/-- Original chart coefficients compute the descended sheaf on the chart image. -/
def relativeDescendedCoefficientImageSectionsIso (U : X.affineOpens) :
    let := closedBaseAlgebra J f U.1
    Γ(relativeDescendedCoefficientSheaf J f, relativeTensorImageOpen J f U) ≅
      (forget₂ (ModuleCat (RelativeAlgebra J f U)) AddCommGrpCat).obj
        (relativeChartCoefficient J f U) := by
  let := closedBaseAlgebra J f U.1
  exact relativeDescendedCoefficientProjectionIso J f U _ le_rfl ≪≫
    relativeAmbientCoefficientTopIso J f U ≪≫
    ((forget₂ (ModuleCat (RelativeAlgebra J f U)) AddCommGrpCat).mapIso
      (relativeChartCoefficientSectionsIso J f U)).symm

end FLT.Mazur.IdealAdicGradedPullback
