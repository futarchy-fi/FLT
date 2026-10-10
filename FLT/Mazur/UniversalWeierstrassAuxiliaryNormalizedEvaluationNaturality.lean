/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedFrame
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationNatural

/-!
# Normalized coordinates commute with arbitrary ring maps

The transformation equations characterize the actual normalized evaluation.
Mapping those equations proves naturality without unfolding coordinate quotients.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : Type} [CommRing R] [CommRing S]
  (g : AuxiliarySectionRing →+* R)

/-- The original X-coordinate is the transformed normalized X-coordinate. -/
theorem auxiliaryNormalizedEvaluation_x_equation (a : Labels 4) (ha : a ≠ 1) :
    ((auxiliaryFrameChange g).u : R) ^ 2 *
      auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 0) +
        (auxiliaryFrameChange g).r = g (auxiliaryCoordinate a ha 0) := by
  have h := DFunLike.congr_fun (auxiliaryNormalizedEvaluation_comp g a ha)
    (coord (auxiliaryPullbackEquation g) 2 0)
  simpa only [AlgHom.comp_apply, affineVariableChangeMap_x, map_add, map_mul, map_pow,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    auxiliaryPullbackEvaluation_coord] using h

/-- The original Y-coordinate is the transformed normalized Y-coordinate. -/
theorem auxiliaryNormalizedEvaluation_y_equation (a : Labels 4) (ha : a ≠ 1) :
    ((auxiliaryFrameChange g).u : R) ^ 3 *
      auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 1) +
        ((auxiliaryFrameChange g).u : R) ^ 2 * (auxiliaryFrameChange g).s *
          auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 0) +
            (auxiliaryFrameChange g).t = g (auxiliaryCoordinate a ha 1) := by
  have h := DFunLike.congr_fun (auxiliaryNormalizedEvaluation_comp g a ha)
    (coord (auxiliaryPullbackEquation g) 2 1)
  simpa only [AlgHom.comp_apply, affineVariableChangeMap_y, map_add, map_mul, map_pow,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    auxiliaryPullbackEvaluation_coord] using h

/-- Every normalized coordinate commutes with arbitrary coefficient-ring changes. -/
theorem auxiliaryNormalizedEvaluation_coordinate_natural (k : R →+* S)
    (a : Labels 4) (ha : a ≠ 1) (i : Fin 3) :
    auxiliaryNormalizedEvaluation (k.comp g) a ha
        (coord (auxiliaryNormalizedEquation (k.comp g)) 2 i) =
      k (auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 i)) := by
  have h := auxiliaryNormalizedEvaluation_coordinates (k.comp g) a ha
    (k (auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 0)))
    (k (auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 1)))
  have hx := congrArg k (auxiliaryNormalizedEvaluation_x_equation g a ha)
  have hy := congrArg k (auxiliaryNormalizedEvaluation_y_equation g a ha)
  rw [auxiliaryFrameChange_natural] at h
  simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass] at h
  simp only [map_add, map_mul, map_pow] at hx hy
  have hxy := h hx hy
  fin_cases i
  · exact hxy.1
  · exact hxy.2
  · change auxiliaryNormalizedEvaluation (k.comp g) a ha
      (coord (auxiliaryNormalizedEquation (k.comp g)) 2 2) =
        k (auxiliaryNormalizedEvaluation g a ha (coord (auxiliaryNormalizedEquation g) 2 2))
    simp only [coord_self, map_one]

end FLT.Mazur.UniversalWeierstrass
