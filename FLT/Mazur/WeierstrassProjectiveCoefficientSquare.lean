/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassIntegralProjectiveMap
public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.ProjectiveSpaceCoefficientMap

/-!
# The original proper cubic embedding commutes with coefficient extension

The square is proved on actual projective chart rings and then on the glued
proper cubic. This retains the ambient projective map needed to compare full
normalization families under arbitrary coefficient maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The actual projective chart quotient commutes with coefficient extension. -/
theorem projectiveChartAlgebra_coefficient (j : Fin 3) :
    (chartCoefficientMap (S := S) W j).toRingHom.comp (projectiveChartAlgebra W j).toRingHom =
      (projectiveChartAlgebra (W.map (algebraMap R S)) j).toRingHom.comp
        (ProjectiveSpace.coefficientChartRingMap (algebraMap R S) (Fin 3) j) := by
  apply ProjectiveSpace.chartRing_hom_ext R (Fin 3) j
  · intro r
    change chartCoefficientMap W j (projectiveChartAlgebra W j (algebraMap R _ r)) = _
    rw [AlgHom.commutes, AlgHom.commutes]
    change _ = projectiveChartAlgebra (W.map (algebraMap R S)) j
      (ProjectiveSpace.coefficientChartRingMap (algebraMap R S) (Fin 3) j
        (ProjectiveSpace.chartScalars R (Fin 3) j r))
    rw [ProjectiveSpace.coefficientChartRingMap_scalar]
    exact (IsScalarTower.algebraMap_apply R S _ r).trans
      ((projectiveChartAlgebra (W.map (algebraMap R S)) j).commutes _).symm
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      projectiveChartAlgebra_coordinate, ProjectiveSpace.coefficientChartRingMap_coordinate,
      chartCoefficientMap_coord]

/-- Each original cubic chart gives the actual commuting projective coefficient square. -/
@[reassoc] theorem projectiveChartMap_coefficient (j : Fin 3) :
    chartCoefficientMorphism (S := S) W j ≫ projectiveChartMap W j =
      projectiveChartMap (W.map (algebraMap R S)) j ≫
        ProjectiveSpace.coefficientMap (algebraMap R S) (Fin 3) := by
  simp only [projectiveChartMap, Category.assoc, ProjectiveSpace.chartMap_coefficientMap]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (fun z ↦ z ≫ ProjectiveSpace.chartMap R (Fin 3) j)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact projectiveChartAlgebra_coefficient (S := S) W j

/-- The entire proper cubic embedding commutes with the original coefficient map. -/
@[reassoc] theorem integralProjectiveMap_coefficient :
    integralCoefficientMorphism (S := S) W ≫ integralProjectiveMap W =
      integralProjectiveMap (W.map (algebraMap R S)) ≫
        ProjectiveSpace.coefficientMap (algebraMap R S) (Fin 3) := by
  apply integralCurve_hom_ext
  intro j
  rw [integralCurveChart_coefficientMorphism_assoc, integralCurveChart_projectiveMap,
    integralCurveChart_projectiveMap_assoc, projectiveChartMap_coefficient]

end FLT.Mazur.WeierstrassIntegralChart
