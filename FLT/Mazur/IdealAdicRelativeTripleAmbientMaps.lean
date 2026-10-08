/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAmbientCoefficient
public import FLT.Mazur.IdealAdicRelativeTripleCoefficientMaps
public import FLT.Mazur.ModuleSheafOverlapCoordinateRefinement

/-!
# Ambient triple coefficient maps

Normalize the ambient pair comparisons to the triple structure map and
identify them with the previously constructed coordinate coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOverlapImageTransition SheafPullbackMapNormalization

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso relativeTensorChart
attribute [local irreducible] relativeTensorTransition relativeTensorOverlapChart
attribute [local irreducible] relativeCoefficientAffineOverlap
attribute [local irreducible] relativeTripleLastPairProjection relativeTripleOuterPairProjection

variable (U V T : X.affineOpens)

/-- The first ambient pair comparison pulled back to the triple overlap. -/
def relativeTripleFirstAmbientMap :
    (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f U) ⟶
      (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f V) :=
  SheafPullbackMapNormalization.normalize (M := (pushforward (relativeTensorChart J f U)).obj
      (relativeChartCoefficientSheaf J f U))
    (N := (pushforward (relativeTensorChart J f V)).obj
      (relativeChartCoefficientSheaf J f V)) (relativeTripleFirstPairProjection J f U V T)
    (relativeOverlapToScheme J f U V) (relativeOverlapToScheme J f U V)
    (relativeTripleToScheme J f U V T) (relativeTripleToScheme J f U V T)
    rfl rfl
    (relativeOverlapAmbientCoefficientIso J f U V).hom

/-- The first ambient triple map recovers its original coordinate comparison. -/
@[reassoc]
lemma relativeTripleFirstAmbientMap_coordinate :
    relativeTripleFirstAmbientMap J f U V T ≫
        (relativeTripleSecondAmbientCoordinate J f U V T).hom =
      (relativeTripleFirstAmbientCoordinate J f U V T).hom ≫
        relativeTripleFirstCoefficientMap J f U V T := by
  unfold relativeTripleFirstAmbientMap relativeTripleSecondAmbientCoordinate
    relativeTripleFirstAmbientCoordinate relativeOverlapAmbientCoefficientIso
    relativeTripleFirstCoefficientMap relativeAmbientCoefficient
  exact ambientIso_refine_coordinate
    (M := relativeChartCoefficientSheaf J f U)
    (N := relativeChartCoefficientSheaf J f V)
    (relativeTripleFirstPairProjection J f U V T)
    (relativeTensorChart J f U) (relativeTensorChart J f V)
    (relativeOverlapFirstProjection J f U V)
    (relativeOverlapSecondProjection J f U V) (relativeOverlapToScheme J f U V)
    rfl Limits.pullback.condition.symm
    (relativeTripleFirstProjection J f U V T) (relativeTripleSecondProjection J f U V T)
    (relativeTripleToScheme J f U V T) rfl rfl
    rfl (relativeTripleFirstProjection_toScheme J f U V T)
    (relativeTripleSecondProjection_toScheme J f U V T) (relativeOverlapCoefficientIso J f U V)

/-- The last ambient pair comparison pulled back to the triple overlap. -/
def relativeTripleLastAmbientMap :
    (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f V) ⟶
      (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f T) :=
  SheafPullbackMapNormalization.normalize (M := (pushforward (relativeTensorChart J f V)).obj
      (relativeChartCoefficientSheaf J f V))
    (N := (pushforward (relativeTensorChart J f T)).obj
      (relativeChartCoefficientSheaf J f T)) (relativeTripleLastPairProjection J f U V T)
    (relativeOverlapToScheme J f V T) (relativeOverlapToScheme J f V T)
    (relativeTripleToScheme J f U V T) (relativeTripleToScheme J f U V T)
    (relativeTripleLastPairProjection_toScheme J f U V T)
    (relativeTripleLastPairProjection_toScheme J f U V T)
    (relativeOverlapAmbientCoefficientIso J f V T).hom

/-- The last ambient triple map recovers its original coordinate comparison. -/
@[reassoc]
lemma relativeTripleLastAmbientMap_coordinate :
    relativeTripleLastAmbientMap J f U V T ≫
        (relativeTripleThirdAmbientCoordinate J f U V T).hom =
      (relativeTripleSecondAmbientCoordinate J f U V T).hom ≫
        relativeTripleLastCoefficientMap J f U V T := by
  unfold relativeTripleLastAmbientMap relativeTripleThirdAmbientCoordinate
    relativeTripleSecondAmbientCoordinate relativeOverlapAmbientCoefficientIso
    relativeTripleLastCoefficientMap relativeAmbientCoefficient
  exact ambientIso_refine_coordinate
    (M := relativeChartCoefficientSheaf J f V)
    (N := relativeChartCoefficientSheaf J f T)
    (relativeTripleLastPairProjection J f U V T)
    (relativeTensorChart J f V) (relativeTensorChart J f T)
    (relativeOverlapFirstProjection J f V T)
    (relativeOverlapSecondProjection J f V T) (relativeOverlapToScheme J f V T)
    rfl Limits.pullback.condition.symm
    (relativeTripleSecondProjection J f U V T) (relativeTripleThirdProjection J f U V T)
    (relativeTripleToScheme J f U V T) (relativeTripleLastPairProjection_second J f U V T)
    (relativeTripleLastPairProjection_third J f U V T)
    (relativeTripleLastPairProjection_toScheme J f U V T)
    (relativeTripleSecondProjection_toScheme J f U V T)
    (relativeTripleThirdProjection_toScheme J f U V T) (relativeOverlapCoefficientIso J f V T)

/-- The outer ambient pair comparison pulled back to the triple overlap. -/
def relativeTripleOuterAmbientMap :
    (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f U) ⟶
      (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f T) :=
  SheafPullbackMapNormalization.normalize (M := (pushforward (relativeTensorChart J f U)).obj
      (relativeChartCoefficientSheaf J f U))
    (N := (pushforward (relativeTensorChart J f T)).obj
      (relativeChartCoefficientSheaf J f T)) (relativeTripleOuterPairProjection J f U V T)
    (relativeOverlapToScheme J f U T) (relativeOverlapToScheme J f U T)
    (relativeTripleToScheme J f U V T) (relativeTripleToScheme J f U V T)
    (relativeTripleOuterPairProjection_toScheme J f U V T)
    (relativeTripleOuterPairProjection_toScheme J f U V T)
    (relativeOverlapAmbientCoefficientIso J f U T).hom

/-- The outer ambient triple map recovers its original coordinate comparison. -/
@[reassoc]
lemma relativeTripleOuterAmbientMap_coordinate :
    relativeTripleOuterAmbientMap J f U V T ≫
        (relativeTripleThirdAmbientCoordinate J f U V T).hom =
      (relativeTripleFirstAmbientCoordinate J f U V T).hom ≫
        relativeTripleOuterCoefficientMap J f U V T := by
  unfold relativeTripleOuterAmbientMap relativeTripleThirdAmbientCoordinate
    relativeTripleFirstAmbientCoordinate relativeOverlapAmbientCoefficientIso
    relativeTripleOuterCoefficientMap relativeAmbientCoefficient
  exact ambientIso_refine_coordinate
    (M := relativeChartCoefficientSheaf J f U)
    (N := relativeChartCoefficientSheaf J f T)
    (relativeTripleOuterPairProjection J f U V T)
    (relativeTensorChart J f U) (relativeTensorChart J f T)
    (relativeOverlapFirstProjection J f U T)
    (relativeOverlapSecondProjection J f U T) (relativeOverlapToScheme J f U T)
    rfl Limits.pullback.condition.symm
    (relativeTripleFirstProjection J f U V T) (relativeTripleThirdProjection J f U V T)
    (relativeTripleToScheme J f U V T) (relativeTripleOuterPairProjection_first J f U V T)
    (relativeTripleOuterPairProjection_third J f U V T)
    (relativeTripleOuterPairProjection_toScheme J f U V T)
    (relativeTripleFirstProjection_toScheme J f U V T)
    (relativeTripleThirdProjection_toScheme J f U V T) (relativeOverlapCoefficientIso J f U T)

end FLT.Mazur.IdealAdicGradedPullback
