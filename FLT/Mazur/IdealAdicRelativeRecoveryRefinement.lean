/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAffineRecovery

/-!
# Refinement compatibility of descended coefficient recovery

The canonical recovery isomorphisms commute with the original coefficient
restriction maps and the geometric comparison of composite pullback paths.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineIteratedPullbackSections

/-- The objectwise pullback comparison is the component of the path comparison. -/
lemma compositeIso_eq_path {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (h : f ≫ g = k) (M : Z.Modules) :
    compositeIso f g k h M = (SheafPullbackPathComparison.comparison f g k h).app M := rfl

end FLT.Mazur.AffineIteratedPullbackSections

namespace FLT.Mazur.IdealAdicGradedPullback

open ModuleSheafOverlapImageTransition SheafPullbackPathComparison

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local instance] relativeTensorChart_isOpenImmersion
attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeTensorChart relativeTensorTransition
attribute [local irreducible] relativeDescendedCoefficientSheaf
attribute [local irreducible] relativeDescendedCoefficientProjection
attribute [local irreducible] relativeCoefficientSheafMap

/-- The coefficient composite wrapper is the path comparison evaluated on its module. -/
lemma relativeCoefficientCompositeIso_eq_path {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    relativeCoefficientCompositeIso J f i j =
      (comparison (relativeTensorTransition J f i) (relativeTensorTransition J f j)
        (relativeTensorTransition J f (i ≫ j)) (relativeTensorTransition_comp J f i j)).app
          (relativeChartCoefficientSheaf J f W) :=
  (relativeCoefficientCompositeIso_eq_chart J f i j).trans
    (AffineIteratedPullbackSections.compositeIso_eq_path _ _ _ _ _)

/-- Coordinate projections commute with a further original affine refinement. -/
lemma relativeDescendedAffineProjection_refine {U W T : X.affineOpens}
    (i : W.1 ⟶ U.1) (k : T.1 ⟶ W.1) :
    (pullback (relativeTensorTransition J f k)).map (relativeDescendedAffineProjection J f i) ≫
        (relativeCoefficientCompositeIso J f k i).hom =
      (comparison (relativeTensorTransition J f k) (relativeTensorChart J f W)
        (relativeTensorChart J f T) (relativeTensorTransition_chart J f k)).hom.app
          (relativeDescendedCoefficientSheaf J f) ≫
        relativeDescendedAffineProjection J f (k ≫ i) := by
  rw [relativeCoefficientCompositeIso_eq_path]
  unfold relativeDescendedAffineProjection relativeAffineCoefficientCoordinate
    relativeAmbientCoefficient
  simp only [Iso.app_hom]
  rw [Functor.map_comp, Category.assoc,
    coordinateIso_refine (relativeTensorTransition J f k) (relativeTensorTransition J f i)
      (relativeTensorChart J f U) (relativeTensorChart J f W)
      (relativeTensorTransition_chart J f i) (relativeTensorTransition J f (k ≫ i))
      (relativeTensorChart J f T) (relativeTensorTransition_comp J f k i)
      (relativeTensorTransition_chart J f k) (relativeTensorTransition_chart J f (k ≫ i))
      (relativeChartCoefficientSheaf J f U)]
  rw [← Category.assoc]
  have h := (comparison (relativeTensorTransition J f k) (relativeTensorChart J f W)
    (relativeTensorChart J f T) (relativeTensorTransition_chart J f k)).hom.naturality
      (X := relativeDescendedCoefficientSheaf J f)
      (Y := (pushforward (relativeTensorChart J f U)).obj (relativeChartCoefficientSheaf J f U))
      (relativeDescendedCoefficientProjection J f U)
  dsimp only [Functor.comp_map] at h
  rw [h, Category.assoc]

/-- Recovery commutes with the original coefficient restriction along every affine refinement. -/
lemma relativeDescendedAffineRecoveryIso_refine {U W T : X.affineOpens}
    (i : W.1 ⟶ U.1) (k : T.1 ⟶ W.1) :
    (pullback (relativeTensorTransition J f k)).map
        (relativeDescendedAffineRecoveryIso J f i).hom ≫ relativeCoefficientSheafMap J f k =
      (comparison (relativeTensorTransition J f k) (relativeTensorChart J f W)
        (relativeTensorChart J f T) (relativeTensorTransition_chart J f k)).hom.app
          (relativeDescendedCoefficientSheaf J f) ≫
        (relativeDescendedAffineRecoveryIso J f (k ≫ i)).hom := by
  change (pullback (relativeTensorTransition J f k)).map
      (relativeDescendedAffineProjection J f i ≫ relativeCoefficientSheafMap J f i) ≫ _ =
    _ ≫ (relativeDescendedAffineProjection J f (k ≫ i) ≫
      relativeCoefficientSheafMap J f (k ≫ i))
  rw [Functor.map_comp, Category.assoc, relativeCoefficientSheafMap_comp_forward,
    ← Category.assoc, relativeDescendedAffineProjection_refine, Category.assoc]

end FLT.Mazur.IdealAdicGradedPullback
