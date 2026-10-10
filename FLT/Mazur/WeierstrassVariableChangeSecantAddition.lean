/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSecant

/-!
# The actual secant addition commutes with admissible changes

Equality is proved in the original localized coordinate algebras, without
passing to geometric points or imposing reducedness on the base.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The localized addition square commutes on the original coordinate algebras. -/
theorem secantVariableChange_addition :
    (secantVariableChange W V C h).comp (secantAddition W) =
      (secantAddition V).comp (affineVariableChangeMap W V C h) := by
  have hx := WeierstrassVariableChangeAdditionFormula.addX
    (W.map (algebraMap R (SecantChart V))) (C.map (algebraMap R (SecantChart V)))
    (secantRestriction V (productX₁ V)) (secantRestriction V (productX₂ V)) (secantSlope V)
  have hy := WeierstrassVariableChangeAdditionFormula.addY
    (W.map (algebraMap R (SecantChart V))) (C.map (algebraMap R (SecantChart V)))
    (secantRestriction V (productX₁ V)) (secantRestriction V (productX₂ V))
    (secantRestriction V (productY₁ V)) (secantSlope V)
  simp only [WeierstrassCurve.toAffine, map_variableChange, h] at hx hy
  simp only [VariableChange.map, Units.coe_map,
    MonoidHom.coe_ofClass] at hx hy
  apply hom_ext
  intro i
  fin_cases i
  · change secantVariableChange W V C h (secantAddition W (coord W 2 0)) =
      secantAddition V (affineVariableChangeMap W V C h (coord W 2 0))
    simpa only [WeierstrassCurve.toAffine, AlgHom.comp_apply,
      affineVariableChangeMap_x, secantAddition_coord,
      Matrix.cons_val_zero, Affine.addX, map_add, map_sub, map_mul, map_pow,
      AlgHom.commutes, map_a₁, map_a₂, secantVariableChange_restriction,
      affineProductVariableChange_x₁, affineProductVariableChange_x₂,
      secantVariableChange_slope] using hx
  · change secantVariableChange W V C h (secantAddition W (coord W 2 1)) =
      secantAddition V (affineVariableChangeMap W V C h (coord W 2 1))
    simpa only [WeierstrassCurve.toAffine, AlgHom.comp_apply,
      affineVariableChangeMap_y, secantAddition_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one, Affine.addY, Affine.negY, Affine.negAddY,
      Affine.addX, map_add, map_sub, map_mul, map_pow, map_neg, AlgHom.commutes,
      map_a₁, map_a₂, map_a₃, secantVariableChange_restriction,
      affineProductVariableChange_x₁, affineProductVariableChange_x₂,
      affineProductVariableChange_y₁, secantVariableChange_slope] using hy
  · change secantVariableChange W V C h (secantAddition W (coord W 2 2)) =
      secantAddition V (affineVariableChangeMap W V C h (coord W 2 2))
    simp only [coord_self, map_one]

end FLT.Mazur.WeierstrassIntegralChart
