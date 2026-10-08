/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeProjectionOverlap
public import FLT.Mazur.ModuleSheafProjectionNormalization
public import FLT.Mazur.ModuleSheafOverlapCoordinateRefinement

/-!
# Descended projections on original affine refinements

Normalize the genuine overlap projection equation on any common affine
refinement. In chart coordinates it retains the original coefficient maps.
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
attribute [local irreducible] relativeTensorChart relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart
attribute [local irreducible] relativeOverlapCoefficientIso relativeCoefficientAffineOverlap
attribute [local irreducible] relativeDescendedCoefficientSheaf
attribute [local irreducible] relativeDescendedCoefficientProjection

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- A common affine refinement has its original structure map into the relative scheme. -/
lemma relativeTensorOverlapChart_toScheme {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeTensorOverlapChart J f i j ≫ relativeOverlapToScheme J f U V =
      relativeTensorChart J f W := by
  unfold relativeOverlapToScheme
  rw [← Category.assoc, relativeOverlapFirstProjection_chart, relativeTensorTransition_chart]

/-- The ambient overlap comparison normalized on a common original affine chart. -/
def relativeAffineAmbientComparison {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (relativeTensorChart J f W)).obj (relativeAmbientCoefficient J f U) ⟶
      (pullback (relativeTensorChart J f W)).obj (relativeAmbientCoefficient J f V) :=
  normalize (W := Spec (.of (RelativeAlgebra J f W)))
    (M := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
    (N := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
    (relativeTensorOverlapChart J f i j)
    (relativeOverlapToScheme J f U V) (relativeOverlapToScheme J f U V)
    (relativeTensorChart J f W) (relativeTensorChart J f W)
    (relativeTensorOverlapChart_toScheme J f i j) (relativeTensorOverlapChart_toScheme J f i j)
    (relativeOverlapAmbientCoefficientIso J f U V).hom

/-- The normalized original overlap comparison intertwines descended affine projections. -/
lemma relativeAffineAmbientComparison_projection {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (relativeTensorChart J f W)).map (relativeDescendedCoefficientProjection J f U) ≫
        relativeAffineAmbientComparison J f i j =
      (pullback (relativeTensorChart J f W)).map (relativeDescendedCoefficientProjection J f V) :=
  normalize_projection (W := Spec (.of (RelativeAlgebra J f W)))
    (M := relativeDescendedCoefficientSheaf J f)
    (N := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
    (P := (pushforward (relativeTensorChart J f V)).obj (relativeChartCoefficientSheaf J f V))
    (relativeTensorOverlapChart J f i j) (relativeOverlapToScheme J f U V)
    (relativeTensorChart J f W) (relativeTensorOverlapChart_toScheme J f i j) _ _ _
    (relativeDescendedCoefficientProjection_overlap J f U V)

/-- The affine coordinate of an ambient chart module on a refinement. -/
def relativeAffineCoefficientCoordinate {U W : X.affineOpens} (i : W.1 ⟶ U.1) :
    (pullback (relativeTensorChart J f W)).obj (relativeAmbientCoefficient J f U) ≅
      (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f U) :=
  coordinateIso (relativeTensorTransition J f i) (relativeTensorChart J f U)
    (relativeTensorChart J f W) (relativeTensorTransition_chart J f i)
    (relativeChartCoefficientSheaf J f U)

/-- In affine coordinates the ambient comparison is the original coefficient comparison. -/
lemma relativeAffineAmbientComparison_coordinate_normalized {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeAffineAmbientComparison J f i j ≫ (relativeAffineCoefficientCoordinate J f j).hom =
      (relativeAffineCoefficientCoordinate J f i).hom ≫
        relativeOverlapCoefficientAffineMap J f i j := by
  unfold relativeAffineAmbientComparison relativeAffineCoefficientCoordinate
    relativeOverlapAmbientCoefficientIso relativeOverlapCoefficientAffineMap
    relativeAmbientCoefficient
  exact ambientIso_refine_coordinate (W := Spec (.of (RelativeAlgebra J f W)))
    (M := relativeChartCoefficientSheaf J f U)
    (N := relativeChartCoefficientSheaf J f V) (relativeTensorOverlapChart J f i j)
    (relativeTensorChart J f U) (relativeTensorChart J f V)
    (relativeOverlapFirstProjection J f U V) (relativeOverlapSecondProjection J f U V)
    (relativeOverlapToScheme J f U V) rfl Limits.pullback.condition.symm
    (relativeTensorTransition J f i) (relativeTensorTransition J f j) (relativeTensorChart J f W)
    (relativeOverlapFirstProjection_chart J f i j) (relativeOverlapSecondProjection_chart J f i j)
    (relativeTensorOverlapChart_toScheme J f i j)
    (relativeTensorTransition_chart J f i) (relativeTensorTransition_chart J f j)
    (relativeOverlapCoefficientIso J f U V)

/-- In affine coordinates the comparison is the original coefficient restriction comparison. -/
lemma relativeAffineAmbientComparison_coordinate {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeAffineAmbientComparison J f i j ≫ (relativeAffineCoefficientCoordinate J f j).hom =
      (relativeAffineCoefficientCoordinate J f i).hom ≫
        (relativeCoefficientAffineOverlap J f i j).hom :=
  (relativeAffineAmbientComparison_coordinate_normalized J f i j).trans
    (congrArg (fun a ↦ (relativeAffineCoefficientCoordinate J f i).hom ≫ a)
      (relativeOverlapCoefficientAffineMap_eq J f i j))

/-- The descended affine projection in an original chart's coordinates. -/
def relativeDescendedAffineProjection {U W : X.affineOpens} (i : W.1 ⟶ U.1) :
    (pullback (relativeTensorChart J f W)).obj (relativeDescendedCoefficientSheaf J f) ⟶
      (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f U) :=
  (pullback (relativeTensorChart J f W)).map (relativeDescendedCoefficientProjection J f U) ≫
    (relativeAffineCoefficientCoordinate J f i).hom

/-- Descended projections retain the original comparison on every common affine refinement. -/
lemma relativeDescendedAffineProjection_overlap {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeDescendedAffineProjection J f i ≫ (relativeCoefficientAffineOverlap J f i j).hom =
      relativeDescendedAffineProjection J f j := by
  unfold relativeDescendedAffineProjection
  rw [Category.assoc, ← relativeAffineAmbientComparison_coordinate, ← Category.assoc,
    relativeAffineAmbientComparison_projection]

/-- Applying either original coefficient restriction gives the same descended affine map. -/
lemma relativeDescendedAffineProjection_restriction {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeDescendedAffineProjection J f i ≫ relativeCoefficientSheafMap J f i =
      relativeDescendedAffineProjection J f j ≫ relativeCoefficientSheafMap J f j := by
  rw [← relativeCoefficientAffineOverlap_hom_comp J f i j, ← Category.assoc,
    relativeDescendedAffineProjection_overlap]

end FLT.Mazur.IdealAdicGradedPullback
