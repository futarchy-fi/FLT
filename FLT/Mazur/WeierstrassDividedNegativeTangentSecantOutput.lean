/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeTangentSlope
public import FLT.Mazur.WeierstrassDividedSecantSource
public import FLT.Mazur.WeierstrassAffineNegation

/-!
# Negative tangent outputs agree with the original secant sum

On every common affine refinement, negating the tangent output of the
negative inputs recovers the original secant output. The divided secant
difference supplies cancellation without inverting the original scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "a'" => branchNegativeInput W s b3 b4 b6 a
local notation "c'" => branchNegativeInput W s b3 b4 b6 c
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "T'" => DividedTangentRing W s b3 b4 b6 a' c'
variable (e : DividedTangentRing W s b3 b4 b6
    (branchNegativeInput W s b3 b4 b6 a) (branchNegativeInput W s b3 b4 b6 c) →ₐ[R] B)
  (f : DividedSecantRing W s b3 b4 b6 a c →ₐ[R] B)
  (h : e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6
        (branchNegativeInput W s b3 b4 b6 a) (branchNegativeInput W s b3 b4 b6 c))) =
    f.comp (IsScalarTower.toAlgHom R S (DividedSecantRing W s b3 b4 b6 a c)))

include h in
/-- A negative tangent slope is minus the original secant slope minus the first coefficient. -/
theorem dividedNegativeTangentSecant_slope :
    e (dividedTangentSlope W s b3 b4 b6 a' c') =
      -f (dividedSecantSlope W s b3 b4 b6 a c) - algebraMap R B W.a₁ := by
  have hj (z : S) : e (algebraMap S T' z) = f (algebraMap S T z) :=
    DFunLike.congr_fun h z
  have he := dividedTangentRefinement_line W s b3 b4 b6 a' c' e
  have hf := congrArg f (dividedSecantSlope_relation W s b3 b4 b6 a c)
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := T)
    (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))).map f
  apply hu.mul_left_inj.mp
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    branchNegativeInput_x, branchNegativeInput_y, map_sub, map_mul,
    map_neg, hj, AlgHom.commutes] at he hf ⊢
  linear_combination he + hf

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h in
/-- Negating the negative-input tangent output recovers the original secant output. -/
theorem dividedNegativeTangentSecant_output :
    (e.comp (dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)).comp
        (WeierstrassIntegralChart.affineNegation W) =
      f.comp (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6) := by
  have hj (z : S) : e (algebraMap S T' z) = f (algebraMap S T z) :=
    DFunLike.congr_fun h z
  have hl := dividedNegativeTangentSecant_slope W s b3 b4 b6 a c e f h
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change e ((dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)
        (WeierstrassIntegralChart.affineNegation W (WeierstrassIntegralChart.coord W 2 0))) =
      f (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0))
    simp only [WeierstrassIntegralChart.affineNegation_x, dividedTangentOutput, dividedSecantOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    simp only [WeierstrassCurve.toAffine, dividedSecantX, dividedTangentX,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', branchNegativeInput_x, map_add, map_sub, map_mul,
      map_pow, AlgHom.commutes, hj, hl]
    ring
  · change e ((dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)
        (WeierstrassIntegralChart.affineNegation W (WeierstrassIntegralChart.coord W 2 1))) =
      f (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1))
    simp only [WeierstrassIntegralChart.affineNegation_y, map_sub, map_neg, map_mul,
      AlgHom.commutes, dividedTangentOutput, dividedSecantOutput,
      WeierstrassIntegralChart.evaluation_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [WeierstrassCurve.toAffine, dividedTangentX,
      dividedTangentY, dividedSecantY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', branchNegativeInput_x,
      branchNegativeInput_y, map_add, map_sub, map_mul, map_pow, map_neg,
      AlgHom.commutes, hj, hl, h3]
    ring
  · change e ((dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)
        (WeierstrassIntegralChart.affineNegation W (WeierstrassIntegralChart.coord W 2 2))) =
      f (dividedSecantOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 2))
    simp only [WeierstrassIntegralChart.coord_self, map_one]

end FLT.Mazur.WeierstrassDilatation
