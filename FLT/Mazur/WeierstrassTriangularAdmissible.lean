/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAdmissibleScale
public import FLT.Mazur.WeierstrassAffineEquationRigidity
public import FLT.Mazur.WeierstrassAffineVariableChangeMap

/-!
# Recovering the admissible equation from an actual triangular map

The leading relation determines a variable change. Equation transport and
uniqueness then prove all its coefficient identities, rather than assuming them.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)
  (f : Coordinate V 2 →ₐ[R] Coordinate W 2) (r t v : R) (s w : Rˣ)
  (hx : f (coord V 2 0) = algebraMap R _ r + algebraMap R _ (s : R) * coord W 2 0)
  (hy : f (coord V 2 1) = algebraMap R _ t + algebraMap R _ v * coord W 2 0 +
    algebraMap R _ (w : R) * coord W 2 1)

include hx hy in
/-- The recovered admissible change transforms the target equation to the source equation. -/
theorem triangularVariableChange_curve : triangularVariableChange r t v s w • V = W := by
  have h := (triangular_coordinate_relations W V f r s t v w hx hy).1
  let C := triangularVariableChange r t v s w
  have hs : (C.u : R) ^ 2 = (s : R) := triangularVariableChange_x r t v s w h
  have hw : (C.u : R) ^ 3 = (w : R) := triangularVariableChange_y r t v s w h
  have hv : (C.u : R) ^ 2 * C.s = v := triangularVariableChange_mixed r t v s w h
  have he : (V.map (algebraMap R (Coordinate W 2))).toAffine.Equation
      (((C.map (algebraMap R (Coordinate W 2))).u : Coordinate W 2) ^ 2 * coord W 2 0 +
        (C.map (algebraMap R (Coordinate W 2))).r)
      (((C.map (algebraMap R (Coordinate W 2))).u : Coordinate W 2) ^ 3 * coord W 2 1 +
        ((C.map (algebraMap R (Coordinate W 2))).u : Coordinate W 2) ^ 2 *
          (C.map (algebraMap R (Coordinate W 2))).s * coord W 2 0 +
          (C.map (algebraMap R (Coordinate W 2))).t) := by
    convert affine_equation_of_hom V f using 1
    · rw [hx]
      simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass, ← map_pow, hs]
      change _ + algebraMap R _ r = _
      ring
    · rw [hy]
      simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass, ← map_pow,
        hw, ← map_mul, hv]
      change _ + _ + algebraMap R _ t = _
      ring
  have he' := (WeierstrassVariableChangeIntegralEquation.equation_iff
    (V.map (algebraMap R _)) (C.map (algebraMap R (Coordinate W 2))) _ _).mp he
  rw [map_variableChange] at he'
  exact affineEquation_curve_eq W (C • V) he'

include hx hy in
/-- The recovered admissible coordinate map equals the original algebra map. -/
theorem triangularVariableChange_map : f =
    affineVariableChangeMap V W (triangularVariableChange r t v s w)
      (triangularVariableChange_curve W V f r t v s w hx hy) := by
  have h := (triangular_coordinate_relations W V f r s t v w hx hy).1
  apply hom_ext
  intro i
  fin_cases i
  · change f (coord V 2 0) = affineVariableChangeMap V W _ _ (coord V 2 0)
    rw [affineVariableChangeMap_x, hx, ← map_pow,
      triangularVariableChange_x r t v s w h]
    change _ = _ + algebraMap R _ r
    ring
  · change f (coord V 2 1) = affineVariableChangeMap V W _ _ (coord V 2 1)
    rw [affineVariableChangeMap_y, hy, ← map_pow, ← map_pow, ← map_mul,
      triangularVariableChange_y r t v s w h, triangularVariableChange_mixed r t v s w h]
    change _ = _ + _ + algebraMap R _ t
    ring
  · change f (coord V 2 2) = affineVariableChangeMap V W _ _ (coord V 2 2)
    simp only [coord_self, map_one]

end FLT.Mazur.WeierstrassIntegralChart
