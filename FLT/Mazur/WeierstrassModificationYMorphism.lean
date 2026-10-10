/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYAlgebra
public import FLT.Mazur.WeierstrassProjectivePointNaturality
public import Mathlib.Tactic.LinearCombination

/-!
# Contraction of the y-direction equation chart

Recover x=u*z and y=z. Multiplying the divided equation by z² and using
r*z=s proves the original cubic over the actual chart algebra.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6 in
/-- The recovered original coordinates satisfy the original homogeneous cubic. -/
theorem original_equation :
    (W.map (algebraMap R (Coordinate W s b3 b4 b6))).toProjective.Equation
      ![coord W s b3 b4 b6 1 * coord W s b3 b4 b6 2, coord W s b3 b4 b6 2, 1] := by
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    h3, h4, h6, map_mul, map_pow, mul_one, one_pow]
  rw [← incidence W s b3 b4 b6]
  linear_combination coord W s b3 b4 b6 2 ^ 2 * equation W s b3 b4 b6

/-- The actual contraction on affine coordinate rings. -/
def fromOriginal : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] Coordinate W s b3 b4 b6 :=
  WeierstrassIntegralChart.evaluation W 2
    ![coord W s b3 b4 b6 1 * coord W s b3 b4 b6 2, coord W s b3 b4 b6 2, 1]
    (original_equation W s b3 b4 b6 h3 h4 h6) rfl

/-- The contraction preserves the original horizontal coordinate. -/
@[simp] theorem fromOriginal_x :
    fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 0) =
      coord W s b3 b4 b6 1 * coord W s b3 b4 b6 2 :=
  WeierstrassIntegralChart.evaluation_coord _ _ _ _ _ _

/-- The contraction preserves the original vertical coordinate. -/
@[simp] theorem fromOriginal_y :
    fromOriginal W s b3 b4 b6 h3 h4 h6 (WeierstrassIntegralChart.coord W 2 1) =
      coord W s b3 b4 b6 2 := WeierstrassIntegralChart.evaluation_coord _ _ _ _ _ _

/-- The actual contraction to the original projective cubic. -/
def toCurve : Spec (.of (Coordinate W s b3 b4 b6)) ⟶
    WeierstrassIntegralChart.integralCurve W :=
  Spec.map (CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom) ≫
    WeierstrassIntegralChart.integralCurveChart W 2

/-- The contraction lies over the original coefficient spectrum. -/
@[reassoc] theorem toCurve_structure :
    toCurve W s b3 b4 b6 h3 h4 h6 ≫ WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W s b3 b4 b6))) :=
  WeierstrassIntegralChart.integralChartPoint_structure W 2 _ _ _

end FLT.Mazur.WeierstrassModificationY
