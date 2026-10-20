/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeTangentSlope
public import FLT.Mazur.WeierstrassAffineNegation

/-!
# Cubic tangent outputs commute with actual negation

Negating the tangent sum of the two negative inputs recovers the original
sum on every common affine refinement. The equality holds in the original
coordinate algebra, without reducedness or scale regularity assumptions.
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
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "T'" => DividedTangentRing W s b3 b4 b6 a' c'
variable (e : DividedTangentRing W s b3 b4 b6
    (branchNegativeInput W s b3 b4 b6 a) (branchNegativeInput W s b3 b4 b6 c) →ₐ[R] B)
  (f : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
  (h : e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6
        (branchNegativeInput W s b3 b4 b6 a) (branchNegativeInput W s b3 b4 b6 c))) =
    f.comp (IsScalarTower.toAlgHom R S (DividedTangentRing W s b3 b4 b6 a c)))

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h in
/-- The negative-input tangent output is the actual original cubic negative. -/
theorem dividedNegativeTangent_output :
    (e.comp (dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)).comp
        (WeierstrassIntegralChart.affineNegation W) =
      f.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) := by
  have hj (z : S) : e (algebraMap S T' z) = f (algebraMap S T z) :=
    DFunLike.congr_fun h z
  have hl := dividedNegativeTangent_slope W s b3 b4 b6 a c e f h
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change e ((dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)
        (WeierstrassIntegralChart.affineNegation W (WeierstrassIntegralChart.coord W 2 0))) =
      f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 0))
    simp only [WeierstrassIntegralChart.affineNegation_x, dividedTangentOutput,
      WeierstrassIntegralChart.evaluation_coord, Matrix.cons_val_zero]
    simp only [WeierstrassCurve.toAffine, dividedTangentX, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom', branchNegativeInput_x, map_add, map_sub, map_mul,
      map_pow, AlgHom.commutes, hj, hl]
    ring
  · change e ((dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)
        (WeierstrassIntegralChart.affineNegation W (WeierstrassIntegralChart.coord W 2 1))) =
      f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 1))
    simp only [WeierstrassIntegralChart.affineNegation_y, map_sub, map_neg, map_mul,
      AlgHom.commutes, dividedTangentOutput, WeierstrassIntegralChart.evaluation_coord,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [WeierstrassCurve.toAffine, dividedTangentX, dividedTangentY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', branchNegativeInput_x,
      branchNegativeInput_y, map_add, map_sub, map_mul, map_pow, map_neg,
      AlgHom.commutes, hj, hl, h3]
    ring
  · change e ((dividedTangentOutput W s b3 b4 b6 a' c' h3 h4 h6)
        (WeierstrassIntegralChart.affineNegation W (WeierstrassIntegralChart.coord W 2 2))) =
      f (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
        (WeierstrassIntegralChart.coord W 2 2))
    simp only [WeierstrassIntegralChart.coord_self, map_one]

end FLT.Mazur.WeierstrassDilatation
