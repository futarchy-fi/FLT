/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeImageTransitionTransport

/-!
# Sealed isomorphisms on actual overlap images

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

/-- The coefficient overlap isomorphism on its actual image, before reindexing. -/
@[irreducible]
def relativeOverlapCoefficientImageIso (U V : X.affineOpens) :
    ((pushforward (relativeTensorChart J f U)).obj
      (relativeChartCoefficientSheaf J f U)).over (relativeOverlapToScheme J f U V).opensRange ≅
    ((pushforward (relativeTensorChart J f V)).obj
      (relativeChartCoefficientSheaf J f V)).over (relativeOverlapToScheme J f U V).opensRange :=
  imageIso (relativeTensorChart J f U) (relativeTensorChart J f V)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeOverlapToScheme J f U V) rfl Limits.pullback.condition.symm
    (relativeOverlapCoefficientIso J f U V)

/-- The original chart transition reindexes the image overlap isomorphism. -/
lemma relativeChartTransition_eq_overlapCoefficientImageIso (U V : X.affineOpens) :
    relativeChartCoefficientImageTransition J f U V =
      Eq.mpr (congrArg (fun A ↦
        ((pushforward (relativeTensorChart J f U)).obj
          (relativeChartCoefficientSheaf J f U)).over A ≅
        ((pushforward (relativeTensorChart J f V)).obj
          (relativeChartCoefficientSheaf J f V)).over A)
        (relativeOverlapToScheme_opensRange J f U V).symm)
        (relativeOverlapCoefficientImageIso J f U V) := by
  unfold relativeOverlapCoefficientImageIso
  exact relativeChartCoefficientImageTransition_eq J f U V

/-- The image overlap morphism extends the specified ambient comparison. -/
lemma relativeOverlapCoefficientImageIso_hom (U V : X.affineOpens) :
    (relativeOverlapCoefficientImageIso J f U V).hom =
      localHom
        (M := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
        (N := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
        (relativeOverlapToScheme J f U V) (relativeOverlapAmbientCoefficientIso J f U V).hom := by
  unfold relativeOverlapCoefficientImageIso
  rw [imageIso_hom, relativeOverlapAmbientCoefficientIso_hom_eq]

end FLT.Mazur.IdealAdicGradedPullback
