/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientGeometricRefinement
public import FLT.Mazur.SheafPullbackObjectwiseRefinement

/-!
# Transport of the original affine coefficient refinement

Specialize coefficient refinement before choosing the geometric overlap.
Keeping the ambient overlap abstract makes the specialization independent
of the scheme presentation used for its pullback projections.
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

variable {O : Scheme.{u}} {U V W Z : X.affineOpens}
variable (i : W.1 ⟶ U.1) (j : W.1 ⟶ V.1) (k : Z.1 ⟶ W.1)

/-- Affine coefficient refinement transports along any compatible geometric chart paths. -/
lemma relativeCoefficientTransport_refine
    (c : (let := closedBaseAlgebra J f W.1; Spec (.of (RelativeAlgebra J f W))) ⟶ O)
    (d : (let := closedBaseAlgebra J f Z.1; Spec (.of (RelativeAlgebra J f Z))) ⟶ O)
    (p : O ⟶ (let := closedBaseAlgebra J f U.1; Spec (.of (RelativeAlgebra J f U))))
    (q : O ⟶ (let := closedBaseAlgebra J f V.1; Spec (.of (RelativeAlgebra J f V))))
    (hi : c ≫ p = relativeTensorTransition J f i)
    (hj : c ≫ q = relativeTensorTransition J f j)
    (hd : relativeTensorTransition J f k ≫ c = d)
    (hi' : d ≫ p = relativeTensorTransition J f (k ≫ i))
    (hj' : d ≫ q = relativeTensorTransition J f (k ≫ j)) :
    (pullback (relativeTensorTransition J f k)).map
        (SheafPullbackLocalComparison.transport c p q
          (relativeTensorTransition J f i) (relativeTensorTransition J f j) hi hj
          (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
          (relativeCoefficientAffineOverlap J f i j).hom) ≫
        (AffineIteratedPullbackSections.compositeIso (relativeTensorTransition J f k)
          c d hd ((pullback q).obj (relativeChartCoefficientSheaf J f V))).hom =
      (AffineIteratedPullbackSections.compositeIso (relativeTensorTransition J f k)
          c d hd ((pullback p).obj (relativeChartCoefficientSheaf J f U))).hom ≫
        SheafPullbackLocalComparison.transport d p q
          (relativeTensorTransition J f (k ≫ i)) (relativeTensorTransition J f (k ≫ j))
          hi' hj' (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
          (relativeCoefficientAffineOverlap J f (k ≫ i) (k ≫ j)).hom := by
  exact SheafPullbackLocalComparison.transport_refine_objectwise
    c p q (relativeTensorTransition J f i) (relativeTensorTransition J f j) hi hj
    (relativeChartCoefficientSheaf J f U) (relativeChartCoefficientSheaf J f V)
    (relativeTensorTransition J f k) d hd
    (relativeTensorTransition J f (k ≫ i)) (relativeTensorTransition J f (k ≫ j))
    (relativeTensorTransition_comp J f k i) (relativeTensorTransition_comp J f k j)
    hi' hj' (relativeCoefficientAffineOverlap J f i j).hom
    (relativeCoefficientAffineOverlap J f (k ≫ i) (k ≫ j)).hom
    (relativeCoefficientAffineOverlap_refine_chart J f i j k)

end FLT.Mazur.IdealAdicGradedPullback
