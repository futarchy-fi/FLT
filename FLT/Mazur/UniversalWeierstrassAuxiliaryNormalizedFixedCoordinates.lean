/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassNormalizedSliceFixed
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedEvaluationNaturality
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedParameter

/-!
# Normalization fixes the original coefficients and every coordinate on the slice

The identity frame change fixes each actual normalized evaluation. The five
universal equation coefficients also identify the original parameter map.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

/-- Equality of the specialized universal equations identifies their parameter maps. -/
theorem parameterHom_eq_of_equation (f g : ParameterRing →+* R)
    (h : smoothEquation.map f = smoothEquation.map g) : f = g := by
  apply parameter_hom_ext
  intro i
  fin_cases i
  · exact congrArg WeierstrassCurve.a₁ h
  · exact congrArg WeierstrassCurve.a₂ h
  · exact congrArg WeierstrassCurve.a₃ h
  · exact congrArg WeierstrassCurve.a₄ h
  · exact congrArg WeierstrassCurve.a₆ h

variable (g : AuxiliarySectionRing →+* R) (hn : SatisfiesNormalization g)

include hn in
/-- The actual coefficient parameter remains unchanged on the original closed slice. -/
theorem auxiliaryNormalizedCoefficientHom_fixed :
    auxiliaryNormalizedCoefficientHom g = auxiliaryCoefficientHom g := by
  apply parameterHom_eq_of_equation
  rw [auxiliaryNormalizedCoefficientHom_equation, normalizedSlice_equation_fixed g hn,
    auxiliaryPullbackEquation_coefficient]

include hn in
/-- Every original labeled coordinate is fixed, not just the four defining relations. -/
theorem auxiliaryNormalizedEvaluation_coordinate_fixed (a : Labels 4) (ha : a ≠ 1)
    (i : Fin 3) :
    auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 i) =
      g (auxiliaryCoordinate a ha i) := by
  have hx := auxiliaryNormalizedEvaluation_x_equation g a ha
  have hy := auxiliaryNormalizedEvaluation_y_equation g a ha
  rw [normalizedSlice_frameChange g hn] at hx hy
  simp only [VariableChange.one_def, Units.val_one, one_pow, one_mul, add_zero, mul_zero,
    zero_mul] at hx hy
  fin_cases i
  · exact hx
  · exact hy
  · change auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 2) =
      g (auxiliaryCoordinate a ha 2)
    rw [coord_self, map_one, auxiliaryPullbackCoordinate_z]

end FLT.Mazur.UniversalWeierstrass
