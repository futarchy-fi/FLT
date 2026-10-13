/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalInfinityTangentUnit
public import FLT.Mazur.WeierstrassVariableChangeUnitChart
public import FLT.Mazur.WeierstrassDividedShearData

/-!
# Root shear on the entire original nodal infinity chart

The inverse variable change lands in the full sheared infinity chart because
its Y coordinate is the proved tangent unit. Its original cubic inclusion is retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
  (r : R) (hr : r ^ 2 + W.a₁ * r - W.a₂ = 0)
local notation "U" => rootShearCurve W r
local notation "C" => VariableChange.mk (1 : Rˣ) 0 r 0
local notation "A" => Coordinate W 1
local notation "u" => nodalInfinityTangentUnit W h₃ h₄ h₆ r hr

/-- The inverse shear's original Y coordinate is exactly the constructed tangent unit. -/
theorem nodalInfinityShear_unit :
    WeierstrassVariableChangeHomogeneous.coordinates
      ((C⁻¹).map (algebraMap R A)) (coord W 1) 1 = (u : A) := by
  simp only [WeierstrassVariableChangeHomogeneous.coordinates, VariableChange.map,
    VariableChange.inv_def, inv_one, Units.val_one, one_pow, one_mul, mul_one,
    zero_mul, sub_zero, neg_zero, map_one, map_zero, add_zero,
    Matrix.cons_val_one, Matrix.cons_val_zero, coord_self, nodalInfinityTangentUnit_val]
  rw [_root_.map_neg]
  ring

/-- The inverse root shear is regular on every point of the original infinity chart. -/
def nodalInfinityShear : chartScheme W 1 ⟶ chartScheme U 1 :=
  variableChangeUnitChart U W C⁻¹ (by rw [rootShearCurve, inv_smul_smul]) 1 1 u
    (nodalInfinityShear_unit W h₃ h₄ h₆ r hr)

/-- The full chart map is the inverse of the actual proper cubic shear on this chart. -/
@[reassoc] theorem nodalInfinityShear_global :
    nodalInfinityShear W h₃ h₄ h₆ r hr ≫ integralCurveChart U 1 =
      integralCurveChart W 1 ≫ (integralVariableChangeIso W U C rfl).inv := by
  rw [nodalInfinityShear, variableChangeUnitChart_global]
  rfl

/-- Reconstructing the original cubic retains its full original infinity inclusion. -/
@[reassoc] theorem nodalInfinityShear_reconstruction :
    nodalInfinityShear W h₃ h₄ h₆ r hr ≫ integralCurveChart U 1 ≫
      (integralVariableChangeIso W U C rfl).hom = integralCurveChart W 1 := by
  rw [nodalInfinityShear_global_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse root shear preserves the original chart's coefficient structure. -/
@[reassoc] theorem nodalInfinityShear_structure :
    nodalInfinityShear W h₃ h₄ h₆ r hr ≫ chartStructure U 1 = chartStructure W 1 := by
  rw [nodalInfinityShear, variableChangeUnitChart_structure]

end FLT.Mazur.WeierstrassIntegralChart
