/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeImageCoefficient
public import FLT.Mazur.IdealAdicRelativeOverlapCoefficientGluing
public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Coefficient transitions on image-open intersections

Transport the actual full-overlap coefficient comparisons to the slice
isomorphisms required by module-sheaf object gluing.
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
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V : X.affineOpens)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeOverlapCoefficientIso

/-- The original chart pushforwards are isomorphic on their image intersection. -/
def relativeChartCoefficientImageTransition :
    ((pushforward (relativeTensorChart J f U)).obj
        (relativeChartCoefficientSheaf J f U)).over
          (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) ≅
      ((pushforward (relativeTensorChart J f V)).obj
        (relativeChartCoefficientSheaf J f V)).over
          (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) := by
  have hr : (relativeOverlapToScheme J f U V).opensRange =
      relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V :=
    TopologicalSpace.Opens.ext (relativeOverlapToScheme_range J f U V)
  rw [← hr]
  exact ModuleSheafOverlapImageTransition.imageIso
    (relativeTensorChart J f U) (relativeTensorChart J f V)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeOverlapToScheme J f U V) rfl Limits.pullback.condition.symm
    (relativeOverlapCoefficientIso J f U V)

/-- The actual image-open coefficient objects have linear transition isomorphisms. -/
def relativeImageCoefficientTransition :
    ((pushforward (relativeTensorImageOpen J f U).ι).obj
        (relativeImageCoefficientSheaf J f U)).over
          (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) ≅
      ((pushforward (relativeTensorImageOpen J f V).ι).obj
        (relativeImageCoefficientSheaf J f V)).over
          (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) :=
  (SheafOfModules.overFunctor (relativeScheme J f).ringCatSheaf
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V)).mapIso
        (relativeImageCoefficientPushforwardIso J f U) ≪≫
    relativeChartCoefficientImageTransition J f U V ≪≫
    ((SheafOfModules.overFunctor (relativeScheme J f).ringCatSheaf
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V)).mapIso
        (relativeImageCoefficientPushforwardIso J f V)).symm

end FLT.Mazur.IdealAdicGradedPullback
