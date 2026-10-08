/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapCoefficientNormalization
public import FLT.Mazur.IdealAdicRelativeTripleProjections
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Coefficient maps on the relative triple overlap

Normalize each pair comparison to the same three coordinate pullbacks.
This makes their composition an equality of actual module-sheaf morphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open SheafPullbackMapNormalization

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U V T : X.affineOpens)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso
attribute [local irreducible] relativeOverlapCoefficientIso

/-- The first pair comparison on common triple-coordinate sheaves. -/
def relativeTripleFirstCoefficientMap :
    (pullback (relativeTripleFirstProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f U) ⟶
      (pullback (relativeTripleSecondProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f V) :=
  normalize (relativeTripleFirstPairProjection J f U V T)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeTripleFirstProjection J f U V T) (relativeTripleSecondProjection J f U V T)
    rfl rfl (relativeOverlapCoefficientIso J f U V).hom

/-- The last pair comparison on common triple-coordinate sheaves. -/
def relativeTripleLastCoefficientMap :
    (pullback (relativeTripleSecondProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f V) ⟶
      (pullback (relativeTripleThirdProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f T) :=
  normalize (relativeTripleLastPairProjection J f U V T)
    (relativeOverlapFirstProjection J f V T) (relativeOverlapSecondProjection J f V T)
    (relativeTripleSecondProjection J f U V T) (relativeTripleThirdProjection J f U V T)
    (relativeTripleLastPairProjection_second J f U V T)
    (relativeTripleLastPairProjection_third J f U V T) (relativeOverlapCoefficientIso J f V T).hom

/-- The outer pair comparison on common triple-coordinate sheaves. -/
def relativeTripleOuterCoefficientMap :
    (pullback (relativeTripleFirstProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f U) ⟶
      (pullback (relativeTripleThirdProjection J f U V T)).obj
        (relativeChartCoefficientSheaf J f T) :=
  normalize (relativeTripleOuterPairProjection J f U V T)
    (relativeOverlapFirstProjection J f U T) (relativeOverlapSecondProjection J f U T)
    (relativeTripleFirstProjection J f U V T) (relativeTripleThirdProjection J f U V T)
    (relativeTripleOuterPairProjection_first J f U V T)
    (relativeTripleOuterPairProjection_third J f U V T) (relativeOverlapCoefficientIso J f U T).hom

/-- The first pair comparison remains invertible on the triple overlap. -/
instance relativeTripleFirstCoefficientMap_isIso :
    IsIso (relativeTripleFirstCoefficientMap J f U V T) := by
  unfold relativeTripleFirstCoefficientMap
  infer_instance

/-- The last pair comparison remains invertible on the triple overlap. -/
instance relativeTripleLastCoefficientMap_isIso :
    IsIso (relativeTripleLastCoefficientMap J f U V T) := by
  unfold relativeTripleLastCoefficientMap
  infer_instance

/-- The outer pair comparison remains invertible on the triple overlap. -/
instance relativeTripleOuterCoefficientMap_isIso :
    IsIso (relativeTripleOuterCoefficientMap J f U V T) := by
  unfold relativeTripleOuterCoefficientMap
  infer_instance

end FLT.Mazur.IdealAdicGradedPullback
