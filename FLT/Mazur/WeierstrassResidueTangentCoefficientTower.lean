/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueInfinityTensorParameter

/-!
# The original residue-tangent coefficient tower on the complete cubic

The two original coefficient maps compose to the direct map, on every
normalized chart and on the whole projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)

/-- Both coefficient steps retain exactly the direct original normalized-chart map. -/
@[reassoc] theorem residueTangentChartCoefficient_comp (j : Fin 3) :
    chartCoefficientMorphism (S := Q) V j ≫
        chartCoefficientMorphism (S := ResidueField R) W j =
      chartCoefficientMorphism (S := Q) W j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (((chartCoefficientMap (S := Q) V j).restrictScalars R).comp
    (chartCoefficientMap (S := ResidueField R) W j)).toRingHom =
      (chartCoefficientMap (S := Q) W j).toRingHom
  congr 1
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  erw [chartCoefficientMap_coord, chartCoefficientMap_coord, chartCoefficientMap_coord]
  rfl

/-- The full original cubic coefficient morphisms compose without replacing the source model. -/
@[reassoc] theorem residueTangentIntegralCoefficient_comp :
    integralCoefficientMorphism (S := Q) V ≫
        integralCoefficientMorphism (S := ResidueField R) W =
      integralCoefficientMorphism (S := Q) W := by
  apply integralCurve_hom_ext
  intro j
  erw [integralCurveChart_coefficientMorphism_assoc,
    integralCurveChart_coefficientMorphism, integralCurveChart_coefficientMorphism,
    residueTangentChartCoefficient_comp_assoc]

end FLT.Mazur.WeierstrassIntegralChart
