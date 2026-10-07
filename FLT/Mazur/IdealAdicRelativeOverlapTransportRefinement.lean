/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientTransportRefinement
public import FLT.Mazur.IdealAdicRelativeOverlapProjections

/-!
# Concrete coefficient refinement using named overlap projections

The transported original affine coefficient comparisons commute with every
further refinement. The spectrum sources and the overlap projections are
explicit so that all pullback functors use the same scheme presentations.
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

attribute [local irreducible] relativeRestriction relativeMap relativeCoefficientSheafMap
attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] compositeIso

/-- The concrete transported coefficient maps refine in their spectrum presentation. -/
lemma relativeOverlapTransport_refine {U V W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1) :
    (pullback (relativeTensorTransition J f k)).map
        (transport (W := Spec (.of (RelativeAlgebra J f W)))
          (relativeTensorOverlapChart J f i j)
          (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
          (relativeTensorTransition J f i) (relativeTensorTransition J f j)
          (relativeOverlapFirstProjection_chart J f i j)
          (relativeOverlapSecondProjection_chart J f i j)
          (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
          (relativeCoefficientAffineOverlap J f i j).hom) ≫
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
        transport (W := Spec (.of (RelativeAlgebra J f Z)))
          (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
          (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
          (relativeTensorTransition J f (k ≫ i)) (relativeTensorTransition J f (k ≫ j))
          (relativeOverlapFirstProjection_chart J f (k ≫ i) (k ≫ j))
          (relativeOverlapSecondProjection_chart J f (k ≫ i) (k ≫ j))
          (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
          (relativeCoefficientAffineOverlap J f (k ≫ i) (k ≫ j)).hom := by
  have h := relativeCoefficientTransport_refine J f i j k
    (relativeTensorOverlapChart J f i j)
    (relativeTensorOverlapChart J f (k ≫ i) (k ≫ j))
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeOverlapFirstProjection_chart J f i j)
    (relativeOverlapSecondProjection_chart J f i j)
    (relativeTensorOverlapChart_refine J f i j k)
    (relativeOverlapFirstProjection_chart J f (k ≫ i) (k ≫ j))
    (relativeOverlapSecondProjection_chart J f (k ≫ i) (k ≫ j))
  exact h

end FLT.Mazur.IdealAdicGradedPullback
