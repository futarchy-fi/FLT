/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassIntegralProjectiveClosed
public import FLT.Mazur.ProjectiveUnitChartPoint

/-!
# Integral cubic points with a unit homogeneous coordinate

Normalization constructs an actual morphism to the original cubic. Its
projective image is the original homogeneous tuple, with no field assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (P : Fin 3 → S)
  (hP : (W.map (algebraMap R S)).toProjective.Equation P)
  (j : Fin 3) (a : Sˣ) (hj : P j = a)

include hP in
/-- Dividing by the chosen unit gives a normalized solution of the same cubic. -/
theorem unit_normalized_equation :
    (W.map (algebraMap R S)).toProjective.Equation (fun i => (a⁻¹ : Sˣ) * P i) :=
  (WeierstrassCurve.Projective.equation_smul P a⁻¹.isUnit).mpr hP

/-- A tuple with a unit coordinate defines a point on the original glued cubic. -/
def integralUnitPoint : Spec (.of S) ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom
    (evaluation W j (fun i => (a⁻¹ : Sˣ) * P i) (unit_normalized_equation W P hP a)
      (by simp [hj])).toRingHom) ≫ integralCurveChart W j

/-- The point retains its exact homogeneous coordinates in projective space. -/
@[reassoc] theorem integralUnitPoint_projectiveMap :
    integralUnitPoint W P hP j a hj ≫ integralProjectiveMap W =
      ProjectiveSpace.unitChartPoint R (Fin 3) (algebraMap R S) P j a hj := by
  rw [integralUnitPoint, Category.assoc, integralCurveChart_projectiveMap]
  simp only [projectiveChartMap, projectiveChartMorphism, ProjectiveSpace.unitChartPoint,
    ← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun f : ProjectiveSpace.chartRing R (Fin 3) j →+* S =>
    Spec.map (CommRingCat.ofHom f) ≫ ProjectiveSpace.chartMap R (Fin 3) j)
  apply ProjectiveSpace.chartRing_hom_ext R (Fin 3) j
  · intro r
    exact (((evaluation W j _ (unit_normalized_equation W P hP a)
      (by simp [hj])).comp (projectiveChartAlgebra W j)).commutes r).trans
      (ProjectiveSpace.unitChartEval_scalar R (Fin 3) _ P j a hj r).symm
  · intro i
    change evaluation W j _ (unit_normalized_equation W P hP a) (by simp [hj])
      (projectiveChartAlgebra W j
      (ProjectiveSpace.coordinate R (Fin 3) j i)) = _
    rw [projectiveChartAlgebra_coordinate, evaluation_coord,
      ProjectiveSpace.unitChartEval_coordinate]

/-- Choosing a different unit coordinate does not change the cubic-valued point. -/
theorem integralUnitPoint_change (k : Fin 3) (b : Sˣ) (hk : P k = b) :
    integralUnitPoint W P hP j a hj = integralUnitPoint W P hP k b hk := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [integralUnitPoint_projectiveMap, integralUnitPoint_projectiveMap]
  exact ProjectiveSpace.unitChartPoint_change R (Fin 3) _ P j k a b hj hk

end FLT.Mazur.WeierstrassIntegralChart
