/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapImageIso

/-!
# Ambient module types for image transitions

General image-open maps retain their section maps under equality transport.
The concrete chart transitions have explicit transport and coordinate formulas.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom
open ModuleSheafOverlapImageTransition

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso relativeTensorChart
attribute [local irreducible] relativeOverlapAmbientCoefficientIso localHom

/-- The overlap image comparison with its named ambient module types. -/
@[irreducible]
def relativeAmbientOverlapImageIso (U V : X.affineOpens) :
    (relativeAmbientCoefficient J f U).over (relativeOverlapToScheme J f U V).opensRange ≅
      (relativeAmbientCoefficient J f V).over (relativeOverlapToScheme J f U V).opensRange :=
  relativeOverlapCoefficientImageIso J f U V

/-- The original chart transition with named ambient module types. -/
@[irreducible]
def relativeAmbientChartImageTransition (U V : X.affineOpens) :
    (relativeAmbientCoefficient J f U).over
        (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) ≅
      (relativeAmbientCoefficient J f V).over
        (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) :=
  relativeChartCoefficientImageTransition J f U V

/-- The ambient chart transition reindexes the overlap image comparison. -/
lemma relativeAmbientChartImageTransition_eq (U V : X.affineOpens) :
    relativeAmbientChartImageTransition J f U V =
      Eq.mpr (congrArg (fun A ↦ (relativeAmbientCoefficient J f U).over A ≅
        (relativeAmbientCoefficient J f V).over A)
        (relativeOverlapToScheme_opensRange J f U V).symm)
        (relativeAmbientOverlapImageIso J f U V) := by
  unfold relativeAmbientChartImageTransition relativeAmbientOverlapImageIso
  exact relativeChartTransition_eq_overlapCoefficientImageIso J f U V

/-- The ambient image comparison extends the actual pullback comparison. -/
lemma relativeAmbientOverlapImageIso_hom (U V : X.affineOpens) :
    (relativeAmbientOverlapImageIso J f U V).hom =
      localHom (M := relativeAmbientCoefficient J f U) (N := relativeAmbientCoefficient J f V)
        (relativeOverlapToScheme J f U V) (relativeOverlapAmbientCoefficientIso J f U V).hom := by
  unfold relativeAmbientOverlapImageIso
  exact relativeOverlapCoefficientImageIso_hom J f U V

end FLT.Mazur.IdealAdicGradedPullback
