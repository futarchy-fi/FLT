/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeIntegralIso

/-!
# Full chart restrictions of variable changes with a unit output coordinate

When the output coordinate is already a unit in the original chart algebra,
normalization gives a map on the entire chart and retains the global cubic map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V) (j k : Fin 3)
local notation "A" => Coordinate V j
local notation "P" => WeierstrassVariableChangeHomogeneous.coordinates
  (C.map (algebraMap R A)) (coord V j)
variable (a : (Coordinate V j)ˣ)
  (ha : WeierstrassVariableChangeHomogeneous.coordinates
    (C.map (algebraMap R (Coordinate V j))) (coord V j) k = a)

include h in
/-- The unnormalized output satisfies the target equation in the original source chart. -/
theorem variableChangeUnitChart_equation : (W.map (algebraMap R A)).toProjective.Equation P := by
  apply (WeierstrassVariableChangeHomogeneous.equation_iff _ _ _).mpr
  rw [map_variableChange, h]
  exact coord_equation V j

/-- The full chart map divides only by the specified unit of the original algebra. -/
def variableChangeUnitChartAlgebra : Coordinate W k →ₐ[R] A :=
  evaluation W k (fun i => (a⁻¹ : Aˣ) * P i)
    (unit_normalized_equation W P (variableChangeUnitChart_equation W V C h j) a)
    (by simp [ha])

/-- The resulting morphism is defined on the whole original source chart. -/
def variableChangeUnitChart : chartScheme V j ⟶ chartScheme W k :=
  Spec.map (CommRingCat.ofHom (variableChangeUnitChartAlgebra W V C h j k a ha).toRingHom)

/-- Every original output coordinate has its normalized homogeneous value. -/
@[simp] theorem variableChangeUnitChartAlgebra_coord (i : Fin 3) :
    variableChangeUnitChartAlgebra W V C h j k a ha (coord W k i) = (a⁻¹ : Aˣ) * P i :=
  evaluation_coord _ _ _ _ _ i

/-- The complete chart morphism is the restriction of the actual global variable change. -/
@[reassoc] theorem variableChangeUnitChart_global :
    variableChangeUnitChart W V C h j k a ha ≫ integralCurveChart W k =
      integralCurveChart V j ≫ (integralVariableChangeIso W V C h).hom := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  change integralUnitPoint W P (variableChangeUnitChart_equation W V C h j) k a ha ≫ _ = _
  rw [integralUnitPoint_projectiveMap]
  change _ = (integralCurveChart V j ≫ integralVariableChangeTo W V C h) ≫ _
  rw [Category.assoc, integralVariableChangeTo_projectiveMap,
    integralCurveChart_projectiveMap_assoc, projectiveChartMap_eq_unitChartPoint]
  exact (WeierstrassVariableChangeLinear.unitChartPoint_projectiveIso C
    (algebraMap R A) (coord V j) j k 1 a (coord_self V j) ha).symm

/-- The full chart map preserves the actual coefficient structure. -/
@[reassoc] theorem variableChangeUnitChart_structure :
    variableChangeUnitChart W V C h j k a ha ≫ chartStructure W k = chartStructure V j := by
  rw [← integralCurveChart_structure, variableChangeUnitChart_global_assoc]
  change integralCurveChart V j ≫ integralVariableChangeTo W V C h ≫ _ = _
  rw [integralVariableChangeTo_structure, integralCurveChart_structure]

end FLT.Mazur.WeierstrassIntegralChart
