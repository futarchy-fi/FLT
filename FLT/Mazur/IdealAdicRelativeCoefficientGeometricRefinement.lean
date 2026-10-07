/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAffineOverlap

/-!
# Geometric normalization of affine coefficient refinement

The coefficient-composition wrapper equals the geometric chart comparison.
This explicit equality keeps concrete tensor definitions out of subsequent
refinement proofs.
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
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeRestriction relativeMap relativeCoefficientSheafMap
attribute [local irreducible] Scheme.Modules.pullback
attribute [local irreducible] relativeTensorTransition
attribute [local irreducible] relativeTensorChart relativeChartCoefficientSheaf
attribute [local irreducible] relativeCoefficientAffineOverlap
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The coefficient composition wrapper is the geometric chart comparison. -/
lemma relativeCoefficientCompositeIso_eq_chart {U V W : X.affineOpens}
    (i : U.1 ⟶ V.1) (j : V.1 ⟶ W.1) :
    relativeCoefficientCompositeIso J f i j =
      AffineIteratedPullbackSections.compositeIso
        (relativeTensorTransition J f i) (relativeTensorTransition J f j)
        (relativeTensorTransition J f (i ≫ j)) (relativeTensorTransition_comp J f i j)
        (relativeChartCoefficientSheaf J f W) := rfl

/-- Affine refinement stated entirely with the geometric chart comparison. -/
lemma relativeCoefficientAffineOverlap_refine_chart {U V W Z : X.affineOpens}
    (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1) :
    (pullback (relativeTensorTransition J f k)).map
          (relativeCoefficientAffineOverlap J f i j).hom ≫
        (AffineIteratedPullbackSections.compositeIso
          (relativeTensorTransition J f k) (relativeTensorTransition J f j)
          (relativeTensorTransition J f (k ≫ j)) (relativeTensorTransition_comp J f k j)
          (relativeChartCoefficientSheaf J f V)).hom =
      (AffineIteratedPullbackSections.compositeIso
          (relativeTensorTransition J f k) (relativeTensorTransition J f i)
          (relativeTensorTransition J f (k ≫ i)) (relativeTensorTransition_comp J f k i)
          (relativeChartCoefficientSheaf J f U)).hom ≫
        (relativeCoefficientAffineOverlap J f (k ≫ i) (k ≫ j)).hom := by
  rw [← relativeCoefficientCompositeIso_eq_chart, ← relativeCoefficientCompositeIso_eq_chart]
  exact relativeCoefficientAffineOverlap_refine J f i j k

end FLT.Mazur.IdealAdicGradedPullback
