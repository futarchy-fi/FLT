/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeImageCoefficientTransition
public import FLT.Mazur.IdealAdicRelativeTripleImageOpen

/-!
# Ambient coefficient comparisons and triple coordinates

The chart pushforwards have actual overlap comparisons. Their pullbacks to
the triple overlap recover the three original coordinate coefficient sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOverlapImageTransition

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso

/-- The ambient module obtained by pushing forward one tensor-chart coefficient sheaf. -/
def relativeAmbientCoefficient (U : X.affineOpens) : (relativeScheme J f).Modules :=
  (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U)

/-- The pair comparison on pullbacks of the ambient coefficient modules. -/
def relativeOverlapAmbientCoefficientIso (U V : X.affineOpens) :
    (pullback (relativeOverlapToScheme J f U V)).obj (relativeAmbientCoefficient J f U) ≅
      (pullback (relativeOverlapToScheme J f U V)).obj (relativeAmbientCoefficient J f V) :=
  ambientIso (relativeTensorChart J f U) (relativeTensorChart J f V)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeOverlapToScheme J f U V) rfl Limits.pullback.condition.symm
    (relativeOverlapCoefficientIso J f U V)

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- The first triple coordinate has the triple structure morphism. -/
@[reassoc]
lemma relativeTripleFirstProjection_toScheme (U V T : X.affineOpens) :
    relativeTripleFirstProjection J f U V T ≫ relativeTensorChart J f U =
      relativeTripleToScheme J f U V T := Category.assoc _ _ _

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- The second triple coordinate has the triple structure morphism. -/
@[reassoc]
lemma relativeTripleSecondProjection_toScheme (U V T : X.affineOpens) :
    relativeTripleSecondProjection J f U V T ≫ relativeTensorChart J f V =
      relativeTripleToScheme J f U V T := by
  rw [relativeTripleSecondThird_condition, ← relativeTripleFirstThird_condition,
    relativeTripleFirstProjection_toScheme]

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- The third triple coordinate has the triple structure morphism. -/
@[reassoc]
lemma relativeTripleThirdProjection_toScheme (U V T : X.affineOpens) :
    relativeTripleThirdProjection J f U V T ≫ relativeTensorChart J f T =
      relativeTripleToScheme J f U V T := by
  rw [← relativeTripleFirstThird_condition, relativeTripleFirstProjection_toScheme]

/-- Recover the first coordinate coefficient sheaf on the triple overlap. -/
def relativeTripleFirstAmbientCoordinate (U V T : X.affineOpens) :
    (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f U) ≅
      (pullback (relativeTripleFirstProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f U) :=
  coordinateIso (relativeTripleFirstProjection J f U V T) (relativeTensorChart J f U)
    (relativeTripleToScheme J f U V T) (relativeTripleFirstProjection_toScheme J f U V T)
    (relativeChartCoefficientSheaf J f U)

/-- Recover the second coordinate coefficient sheaf on the triple overlap. -/
def relativeTripleSecondAmbientCoordinate (U V T : X.affineOpens) :
    (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f V) ≅
      (pullback (relativeTripleSecondProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f V) :=
  coordinateIso (relativeTripleSecondProjection J f U V T) (relativeTensorChart J f V)
    (relativeTripleToScheme J f U V T) (relativeTripleSecondProjection_toScheme J f U V T)
    (relativeChartCoefficientSheaf J f V)

/-- Recover the third coordinate coefficient sheaf on the triple overlap. -/
def relativeTripleThirdAmbientCoordinate (U V T : X.affineOpens) :
    (pullback (relativeTripleToScheme J f U V T)).obj (relativeAmbientCoefficient J f T) ≅
      (pullback (relativeTripleThirdProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f T) :=
  coordinateIso (relativeTripleThirdProjection J f U V T) (relativeTensorChart J f T)
    (relativeTripleToScheme J f U V T) (relativeTripleThirdProjection_toScheme J f U V T)
    (relativeChartCoefficientSheaf J f T)

end FLT.Mazur.IdealAdicGradedPullback
