/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeOverlapCoefficientGluing

/-!
# Affine normalization of the glued coefficient comparisons

The full-overlap isomorphisms recover the original normalized affine maps.
Consequently their normalized restrictions satisfy the affine cocycle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

open SheafPullbackPathComparison

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeTensorTransition
attribute [local irreducible] relativeTensorOverlapChart relativeTensorChart
attribute [local irreducible] relativeChartCoefficientSheaf relativeCoefficientAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- Normalize the restriction of the full-overlap comparison to an affine chart. -/
def relativeOverlapCoefficientAffineMap {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    (pullback (relativeTensorTransition J f i)).obj (relativeChartCoefficientSheaf J f U) ⟶
      (pullback (relativeTensorTransition J f j)).obj (relativeChartCoefficientSheaf J f V) :=
  (comparison (X := Spec (.of (RelativeAlgebra J f W)))
      (relativeTensorOverlapChart J f i j) (relativeOverlapFirstProjection J f U V)
      (relativeTensorTransition J f i) (relativeOverlapFirstProjection_chart J f i j)).inv.app
        (relativeChartCoefficientSheaf J f U) ≫
    (pullback (X := Spec (.of (RelativeAlgebra J f W)))
      (relativeTensorOverlapChart J f i j)).map (relativeOverlapCoefficientIso J f U V).hom ≫
    (comparison (X := Spec (.of (RelativeAlgebra J f W)))
      (relativeTensorOverlapChart J f i j) (relativeOverlapSecondProjection J f U V)
      (relativeTensorTransition J f j) (relativeOverlapSecondProjection_chart J f i j)).hom.app
        (relativeChartCoefficientSheaf J f V)

/-- The normalized global comparison is the original affine coefficient comparison. -/
lemma relativeOverlapCoefficientAffineMap_eq {U V W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) :
    relativeOverlapCoefficientAffineMap J f i j =
      (relativeCoefficientAffineOverlap J f i j).hom := by
  unfold relativeOverlapCoefficientAffineMap
  rw [relativeOverlapCoefficientIso_pullback]
  unfold relativeOverlapSpectrumChartMap SheafPullbackLocalComparison.transport
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The normalized full-overlap comparisons compose on every common affine chart. -/
lemma relativeOverlapCoefficientAffineMap_cocycle {U V T W : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : W.1 ⟶ T.1) :
    relativeOverlapCoefficientAffineMap J f i j ≫
        relativeOverlapCoefficientAffineMap J f j k =
      relativeOverlapCoefficientAffineMap J f i k := by
  rw [relativeOverlapCoefficientAffineMap_eq, relativeOverlapCoefficientAffineMap_eq,
    relativeOverlapCoefficientAffineMap_eq]
  exact relativeCoefficientAffineOverlap_cocycle J f i j k

end FLT.Mazur.IdealAdicGradedPullback
