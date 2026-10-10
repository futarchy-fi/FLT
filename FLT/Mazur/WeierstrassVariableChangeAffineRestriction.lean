/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntegralIso
public import FLT.Mazur.WeierstrassAffineVariableChangeSections

/-!
# The global variable-change isomorphism retains its original affine restriction

The previously constructed affine algebra isomorphism is exactly the affine
restriction of the new proper-cubic isomorphism, as actual scheme morphisms.
-/

@[expose] public noncomputable section

open WeierstrassCurve AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The original affine algebra map has the homogeneous coordinate formula on Z = 1. -/
theorem affineVariableChangeMap_coordinates :
    (fun i => affineVariableChangeMap W V C h (coord W 2 i)) =
      WeierstrassVariableChangeHomogeneous.coordinates
        (C.map (algebraMap R (Coordinate V 2))) (coord V 2) := by
  ext i
  fin_cases i <;>
    simp [WeierstrassVariableChangeHomogeneous.coordinates, VariableChange.map,
      affineVariableChangeMap_x, affineVariableChangeMap_y, coord_self]

/-- The affine isomorphism agrees with the ambient projective substitution. -/
theorem affineVariableChangeIso_projectiveChartMap :
    (affineVariableChangeIso W V C h).hom ≫ projectiveChartMap W 2 =
      projectiveChartMap V 2 ≫ (WeierstrassVariableChangeLinear.projectiveIso C).hom := by
  rw [projectiveChartMap_eq_unitChartPoint, projectiveChartMap_eq_unitChartPoint]
  change Spec.map (CommRingCat.ofHom (affineVariableChangeMap W V C h).toRingHom) ≫ _ = _
  rw [ProjectiveSpace.unitChartPoint_map]
  simp only [map_one]
  have he := WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso C
    (algebraMap R (Coordinate V 2)) (coord V 2) 2 2 1 1 (coord_self V 2)
    (coord_self V 2)
  rw [he]
  congr 1
  · exact (affineVariableChangeMap W V C h).comp_algebraMap
  · exact affineVariableChangeMap_coordinates W V C h

/-- The global isomorphism extends the exact previously constructed affine isomorphism. -/
@[reassoc] theorem integralVariableChangeIso_affine :
    integralCurveChart V 2 ≫ (integralVariableChangeIso W V C h).hom =
      (affineVariableChangeIso W V C h).hom ≫ integralCurveChart W 2 := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  change (integralCurveChart V 2 ≫ integralVariableChangeTo W V C h) ≫ _ = _
  rw [Category.assoc, integralVariableChangeTo_projectiveMap,
    integralCurveChart_projectiveMap_assoc, Category.assoc,
    integralCurveChart_projectiveMap, affineVariableChangeIso_projectiveChartMap]

end FLT.Mazur.WeierstrassIntegralChart
