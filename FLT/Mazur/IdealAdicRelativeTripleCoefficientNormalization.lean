/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeTripleCoefficientMaps

/-!
# Affine restrictions of triple coefficient maps

The three normalized global comparisons recover the original affine maps
on every common refinement of the three tensor charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open SheafPullbackMapNormalization SheafPullbackPathComparison

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso
attribute [local irreducible] relativeOverlapCoefficientIso


/-- The first comparison restricts to its normalized affine pair map. -/
lemma relativeTripleFirstCoefficientMap_chart {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    (pullback (relativeTensorTripleOverlapChart J f i j k)).map
        (relativeTripleFirstCoefficientMap J f U V T) ≫
        (comparison (relativeTensorTripleOverlapChart J f i j k)
          (relativeTripleSecondProjection J f U V T) (relativeTensorTransition J f j)
          (relativeTensorTripleOverlapChart_second J f i j k)).hom.app
            (relativeChartCoefficientSheaf J f V) =
      (comparison (relativeTensorTripleOverlapChart J f i j k)
        (relativeTripleFirstProjection J f U V T) (relativeTensorTransition J f i)
        (relativeTensorTripleOverlapChart_first J f i j k)).hom.app
          (relativeChartCoefficientSheaf J f U) ≫
        relativeOverlapCoefficientAffineMap J f i j := by
  exact normalize_refine (relativeTripleFirstPairProjection J f U V T)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeTripleFirstProjection J f U V T) (relativeTripleSecondProjection J f U V T)
    rfl rfl
    (relativeTensorTripleOverlapChart J f i j k) (relativeTensorOverlapChart J f i j)
    (relativeTensorTripleOverlapChart_firstPair J f i j k)
    (relativeTensorTransition J f i) (relativeTensorTransition J f j)
    (relativeTensorTripleOverlapChart_first J f i j k)
    (relativeTensorTripleOverlapChart_second J f i j k)
    (relativeOverlapFirstProjection_chart J f i j)
    (relativeOverlapSecondProjection_chart J f i j) (relativeOverlapCoefficientIso J f U V).hom

/-- The last comparison restricts to its normalized affine pair map. -/
lemma relativeTripleLastCoefficientMap_chart {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    (pullback (relativeTensorTripleOverlapChart J f i j k)).map
        (relativeTripleLastCoefficientMap J f U V T) ≫
        (comparison (relativeTensorTripleOverlapChart J f i j k)
          (relativeTripleThirdProjection J f U V T) (relativeTensorTransition J f k)
          (relativeTensorTripleOverlapChart_third J f i j k)).hom.app
            (relativeChartCoefficientSheaf J f T) =
      (comparison (relativeTensorTripleOverlapChart J f i j k)
        (relativeTripleSecondProjection J f U V T) (relativeTensorTransition J f j)
        (relativeTensorTripleOverlapChart_second J f i j k)).hom.app
          (relativeChartCoefficientSheaf J f V) ≫
        relativeOverlapCoefficientAffineMap J f j k := by
  exact normalize_refine (relativeTripleLastPairProjection J f U V T)
    (relativeOverlapFirstProjection J f V T) (relativeOverlapSecondProjection J f V T)
    (relativeTripleSecondProjection J f U V T) (relativeTripleThirdProjection J f U V T)
    (relativeTripleLastPairProjection_second J f U V T)
    (relativeTripleLastPairProjection_third J f U V T)
    (relativeTensorTripleOverlapChart J f i j k) (relativeTensorOverlapChart J f j k)
    (relativeTensorTripleOverlapChart_lastPair J f i j k)
    (relativeTensorTransition J f j) (relativeTensorTransition J f k)
    (relativeTensorTripleOverlapChart_second J f i j k)
    (relativeTensorTripleOverlapChart_third J f i j k)
    (relativeOverlapFirstProjection_chart J f j k)
    (relativeOverlapSecondProjection_chart J f j k) (relativeOverlapCoefficientIso J f V T).hom

/-- The outer comparison restricts to its normalized affine pair map. -/
lemma relativeTripleOuterCoefficientMap_chart {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    (pullback (relativeTensorTripleOverlapChart J f i j k)).map
        (relativeTripleOuterCoefficientMap J f U V T) ≫
        (comparison (relativeTensorTripleOverlapChart J f i j k)
          (relativeTripleThirdProjection J f U V T) (relativeTensorTransition J f k)
          (relativeTensorTripleOverlapChart_third J f i j k)).hom.app
            (relativeChartCoefficientSheaf J f T) =
      (comparison (relativeTensorTripleOverlapChart J f i j k)
        (relativeTripleFirstProjection J f U V T) (relativeTensorTransition J f i)
        (relativeTensorTripleOverlapChart_first J f i j k)).hom.app
          (relativeChartCoefficientSheaf J f U) ≫
        relativeOverlapCoefficientAffineMap J f i k := by
  exact normalize_refine (relativeTripleOuterPairProjection J f U V T)
    (relativeOverlapFirstProjection J f U T) (relativeOverlapSecondProjection J f U T)
    (relativeTripleFirstProjection J f U V T) (relativeTripleThirdProjection J f U V T)
    (relativeTripleOuterPairProjection_first J f U V T)
    (relativeTripleOuterPairProjection_third J f U V T)
    (relativeTensorTripleOverlapChart J f i j k) (relativeTensorOverlapChart J f i k)
    (relativeTensorTripleOverlapChart_outerPair J f i j k)
    (relativeTensorTransition J f i) (relativeTensorTransition J f k)
    (relativeTensorTripleOverlapChart_first J f i j k)
    (relativeTensorTripleOverlapChart_third J f i j k)
    (relativeOverlapFirstProjection_chart J f i k)
    (relativeOverlapSecondProjection_chart J f i k) (relativeOverlapCoefficientIso J f U T).hom

end FLT.Mazur.IdealAdicGradedPullback
