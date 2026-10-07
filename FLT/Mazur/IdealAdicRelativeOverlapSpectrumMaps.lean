/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapCoefficientCharts
public import FLT.Mazur.IdealAdicRelativeOverlapTransportRefinement

/-!
# Coefficient maps with canonical spectrum source types

These maps equal the original overlap chart comparisons. Their canonical
source presentation retains the checked refinement law for later gluing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open AffineIteratedPullbackSections SheafPullbackLocalComparison

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] compositeIso

/-- The original local coefficient comparison with an explicit spectrum source. -/
def relativeOverlapSpectrumChartMap {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).obj
        ((pullback (relativeOverlapFirstProjection J f U V)).obj
          (relativeChartCoefficientSheaf J f U)) ⟶
      (pullback (X := Spec (.of (RelativeAlgebra J f W)))
        (relativeTensorOverlapChart J f i j)).obj
        ((pullback (relativeOverlapSecondProjection J f U V)).obj
          (relativeChartCoefficientSheaf J f V)) :=
  transport (W := Spec (.of (RelativeAlgebra J f W)))
    (relativeTensorOverlapChart J f i j)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeTensorTransition J f i) (relativeTensorTransition J f j)
    (relativeOverlapFirstProjection_chart J f i j)
    (relativeOverlapSecondProjection_chart J f i j)
    (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
    (relativeCoefficientAffineOverlap J f i j).hom

/-- Canonical source types retain the original local coefficient morphism. -/
lemma relativeOverlapSpectrumChartMap_eq_original {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeOverlapSpectrumChartMap J f i j = relativeOverlapCoefficientChartMap J f i j := by
  unfold relativeOverlapSpectrumChartMap relativeOverlapCoefficientChartMap
  rfl

/-- The canonical local coefficient comparison is invertible. -/
instance relativeOverlapSpectrumChartMap_isIso {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    IsIso (relativeOverlapSpectrumChartMap J f i j) := by
  unfold relativeOverlapSpectrumChartMap
  infer_instance

/-- The canonical local maps commute with every further affine refinement. -/
lemma relativeOverlapSpectrumChartMap_refine {U V W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1) :
    (pullback (relativeTensorTransition J f k)).map
        (relativeOverlapSpectrumChartMap J f i j) ≫
        (compositeIso (X := Spec (.of (RelativeAlgebra J f Z)))
          (Y := Spec (.of (RelativeAlgebra J f W))) (relativeTensorTransition J f k)
          (relativeTensorOverlapChart J f i j)
          (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
          (relativeTensorOverlapChart_refine J f i j k)
          ((pullback (relativeOverlapSecondProjection J f U V)).obj
            (relativeChartCoefficientSheaf J f V))).hom =
      (compositeIso (X := Spec (.of (RelativeAlgebra J f Z)))
          (Y := Spec (.of (RelativeAlgebra J f W))) (relativeTensorTransition J f k)
          (relativeTensorOverlapChart J f i j)
          (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
          (relativeTensorOverlapChart_refine J f i j k)
          ((pullback (relativeOverlapFirstProjection J f U V)).obj
            (relativeChartCoefficientSheaf J f U))).hom ≫
        relativeOverlapSpectrumChartMap J f (k ≫ i) (k ≫ j) := by
  unfold relativeOverlapSpectrumChartMap
  exact relativeOverlapTransport_refine J f i j k

end FLT.Mazur.IdealAdicGradedPullback
