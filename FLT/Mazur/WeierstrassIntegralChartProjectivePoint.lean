/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassIntegralUnitPoint

/-!
# The original cubic chart as a projective scheme point

The chart's closed embedding agrees with evaluation at its universal tuple.
This comparison retains the original chart morphisms when transporting points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (j : Fin 3)

/-- The ambient chart morphism is the projective point of its universal normalized tuple. -/
theorem projectiveChartMap_eq_unitChartPoint : projectiveChartMap W j =
    ProjectiveSpace.unitChartPoint R (Fin 3) (algebraMap R (Coordinate W j))
      (coord W j) j 1 (coord_self W j) := by
  unfold projectiveChartMap projectiveChartMorphism ProjectiveSpace.unitChartPoint
  apply congrArg (fun f : ProjectiveSpace.chartRing R (Fin 3) j →+* Coordinate W j =>
    Spec.map (CommRingCat.ofHom f) ≫ ProjectiveSpace.chartMap R (Fin 3) j)
  apply ProjectiveSpace.chartRing_hom_ext R (Fin 3) j
  · intro r
    exact ((projectiveChartAlgebra W j).commutes r).trans
      (ProjectiveSpace.unitChartEval_scalar R (Fin 3) _ _ j 1 (coord_self W j) r).symm
  · intro i
    change projectiveChartAlgebra W j (ProjectiveSpace.coordinate R (Fin 3) j i) = _
    simp only [projectiveChartAlgebra_coordinate, ProjectiveSpace.unitChartEval_coordinate,
      inv_one, Units.val_one, one_mul]

end FLT.Mazur.WeierstrassIntegralChart
